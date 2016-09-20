/*
 *  Copyright 2016 Alexey Andreev.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.teavm.model.lowlevel;

import com.carrotsearch.hppc.IntArrayList;
import com.carrotsearch.hppc.IntObjectMap;
import com.carrotsearch.hppc.IntObjectOpenHashMap;
import com.carrotsearch.hppc.cursors.ObjectCursor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.teavm.common.DominatorTree;
import org.teavm.common.Graph;
import org.teavm.common.GraphBuilder;
import org.teavm.common.GraphUtils;
import org.teavm.interop.NoGC;
import org.teavm.model.BasicBlock;
import org.teavm.model.ClassReader;
import org.teavm.model.ClassReaderSource;
import org.teavm.model.Incoming;
import org.teavm.model.Instruction;
import org.teavm.model.MethodReader;
import org.teavm.model.MethodReference;
import org.teavm.model.Phi;
import org.teavm.model.Program;
import org.teavm.model.Variable;
import org.teavm.model.instructions.CloneArrayInstruction;
import org.teavm.model.instructions.ConstructArrayInstruction;
import org.teavm.model.instructions.ConstructInstruction;
import org.teavm.model.instructions.ExitInstruction;
import org.teavm.model.instructions.InitClassInstruction;
import org.teavm.model.instructions.IntegerConstantInstruction;
import org.teavm.model.instructions.InvocationType;
import org.teavm.model.instructions.InvokeInstruction;
import org.teavm.model.instructions.JumpInstruction;
import org.teavm.model.instructions.RaiseInstruction;
import org.teavm.model.util.DefinitionExtractor;
import org.teavm.model.util.GraphColorer;
import org.teavm.model.util.LivenessAnalyzer;
import org.teavm.model.util.ProgramUtils;
import org.teavm.model.util.TypeInferer;
import org.teavm.model.util.UsageExtractor;
import org.teavm.model.util.VariableType;
import org.teavm.runtime.Mutator;

public class GcRootMaintainingTransformer {
    private ClassReaderSource classSource;

    public GcRootMaintainingTransformer(ClassReaderSource classSource) {
        this.classSource = classSource;
    }

    public void apply(Program program, MethodReader method) {
        if (!requiresGc(method.getReference())) {
            return;
        }
        List<IntObjectMap<BitSet>> liveInInformation = findCallSiteLiveIns(program, method);

        Graph interferenceGraph = buildInterferenceGraph(liveInInformation, program);
        boolean[] spilled = getAffectedVariables(liveInInformation, program);
        int[] colors = new int[interferenceGraph.size()];
        new GraphColorer().colorize(interferenceGraph, colors);

        int maxColor = -1;
        for (int color : colors) {
            if (spilled[color]) {
                maxColor = Math.max(maxColor, color);
            }
        }
        if (maxColor < 0) {
            return;
        }
        int usedColors = maxColor + 1;

        // If a variable is spilled to stack, then phi which input this variable also spilled to stack
        // If all of phi inputs are spilled to stack, then we don't need to insert spilling instruction
        // for this phi.
        List<Set<Phi>> destinationPhis = getDestinationPhis(program);
        int[] inputCount = getInputCount(program);
        boolean[] autoSpilled = new boolean[spilled.length];
        for (int i = 0; i < spilled.length; ++i) {
            if (spilled[i]) {
                Set<Phi> phis = destinationPhis.get(i);
                if (phis != null) {
                    for (Phi phi : destinationPhis.get(i)) {
                        int destination = phi.getReceiver().getIndex();
                        spilled[destination] = true;
                        autoSpilled[destination] = --inputCount[destination] == 0;
                    }
                }
            }
        }

        List<IntObjectMap<BitSet>> liveInStores = reduceGcRootStores(program, usedColors, liveInInformation,
                colors, autoSpilled);
        putLiveInGcRoots(program, liveInInformation, liveInStores, colors);
        addStackAllocation(program, usedColors);
        addStackRelease(program, usedColors);
    }

    private List<IntObjectMap<BitSet>> findCallSiteLiveIns(Program program, MethodReader method) {
        Graph cfg = ProgramUtils.buildControlFlowGraph(program);
        TypeInferer typeInferer = new TypeInferer();
        typeInferer.inferTypes(program, method.getReference());
        List<IntObjectMap<BitSet>> liveInInformation = new ArrayList<>();

        LivenessAnalyzer livenessAnalyzer = new LivenessAnalyzer();
        livenessAnalyzer.analyze(program);
        DefinitionExtractor defExtractor = new DefinitionExtractor();
        UsageExtractor useExtractor = new UsageExtractor();

        for (int i = 0; i < program.basicBlockCount(); ++i) {
            BasicBlock block = program.basicBlockAt(i);
            IntObjectMap<BitSet> blockLiveIn = new IntObjectOpenHashMap<>();
            liveInInformation.add(blockLiveIn);
            BitSet currentLiveOut = new BitSet();
            for (int successor : cfg.outgoingEdges(i)) {
                currentLiveOut.or(livenessAnalyzer.liveIn(successor));
            }
            for (int j = block.getInstructions().size() - 1; j >= 0; --j) {
                Instruction insn = block.getInstructions().get(j);
                insn.acceptVisitor(defExtractor);
                insn.acceptVisitor(useExtractor);
                for (Variable usedVar : useExtractor.getUsedVariables()) {
                    currentLiveOut.set(usedVar.getIndex());
                }
                for (Variable definedVar : defExtractor.getDefinedVariables()) {
                    currentLiveOut.clear(definedVar.getIndex());
                }
                if (insn instanceof InvokeInstruction || insn instanceof InitClassInstruction
                        || insn instanceof ConstructInstruction || insn instanceof ConstructArrayInstruction
                        || insn instanceof CloneArrayInstruction || insn instanceof RaiseInstruction) {
                    if (insn instanceof InvokeInstruction && !requiresGc(((InvokeInstruction) insn).getMethod())) {
                        continue;
                    }

                    BitSet csLiveIn = (BitSet) currentLiveOut.clone();
                    for (int v = csLiveIn.nextSetBit(0); v >= 0; v = csLiveIn.nextSetBit(v + 1)) {
                        if (!isReference(typeInferer, v)) {
                            csLiveIn.clear(v);
                        }
                    }
                    csLiveIn.clear(0, method.parameterCount() + 1);
                    blockLiveIn.put(j, csLiveIn);
                }
            }
            if (block.getExceptionVariable() != null) {
                currentLiveOut.clear(block.getExceptionVariable().getIndex());
            }
        }

        return liveInInformation;
    }

    private Graph buildInterferenceGraph(List<IntObjectMap<BitSet>> liveInInformation, Program program) {
        GraphBuilder builder = new GraphBuilder(program.variableCount());
        for (IntObjectMap<BitSet> blockLiveIn : liveInInformation) {
            for (ObjectCursor<BitSet> callSiteLiveIn : blockLiveIn.values()) {
                BitSet liveVarsSet = callSiteLiveIn.value;
                IntArrayList liveVars = new IntArrayList();
                for (int i = liveVarsSet.nextSetBit(0); i >= 0; i = liveVarsSet.nextSetBit(i + 1)) {
                    liveVars.add(i);
                }
                int[] liveVarArray = liveVars.toArray();
                for (int i = 0; i < liveVarArray.length - 1; ++i) {
                    for (int j = i + 1; i < liveVarArray.length; ++j) {
                        builder.addEdge(liveVarArray[i], liveVarArray[j]);
                    }
                }
            }
        }
        return builder.build();
    }

    private boolean[] getAffectedVariables(List<IntObjectMap<BitSet>> liveInInformation, Program program) {
        boolean[] affectedVariables = new boolean[program.variableCount()];
        for (IntObjectMap<BitSet> blockLiveIn : liveInInformation) {
            for (ObjectCursor<BitSet> callSiteLiveIn : blockLiveIn.values()) {
                BitSet liveVarsSet = callSiteLiveIn.value;
                for (int i = liveVarsSet.nextSetBit(0); i >= 0; i = liveVarsSet.nextSetBit(i + 1)) {
                    affectedVariables[i] = true;
                }
            }
        }
        return affectedVariables;
    }

    private List<Set<Phi>> getDestinationPhis(Program program) {
        List<Set<Phi>> destinationPhis = new ArrayList<>();
        destinationPhis.addAll(Collections.nCopies(program.variableCount(), null));

        for (int i = 0; i < program.basicBlockCount(); ++i) {
            BasicBlock block = program.basicBlockAt(i);
            for (Phi phi : block.getPhis()) {
                for (Incoming incoming : phi.getIncomings()) {
                    Set<Phi> phis = destinationPhis.get(incoming.getValue().getIndex());
                    if (phis == null) {
                        phis = new HashSet<>();
                        destinationPhis.set(incoming.getValue().getIndex(), phis);
                    }
                    phis.add(phi);
                }
            }
        }

        return destinationPhis;
    }

    private int[] getInputCount(Program program) {
        int[] inputCount = new int[program.variableCount()];

        for (int i = 0; i < program.basicBlockCount(); ++i) {
            BasicBlock block = program.basicBlockAt(i);
            for (Phi phi : block.getPhis()) {
                inputCount[phi.getReceiver().getIndex()] = phi.getIncomings().size();
            }
        }

        return inputCount;
    }

    private List<IntObjectMap<BitSet>> reduceGcRootStores(Program program, int usedColors,
            List<IntObjectMap<BitSet>> liveInInformation, int[] colors, boolean[] autoSpilled) {
        class Step {
            final int node;
            int[] slotStates = new int[usedColors];
            public Step(int node) {
                this.node = node;
            }
        }

        List<IntObjectMap<BitSet>> slotsToUpdate = new ArrayList<>();
        for (int i = 0; i < program.basicBlockCount(); ++i) {
            slotsToUpdate.add(new IntObjectOpenHashMap<>());
        }

        Graph cfg = ProgramUtils.buildControlFlowGraph(program);
        DominatorTree dom = GraphUtils.buildDominatorTree(cfg);
        Graph domGraph = GraphUtils.buildDominatorGraph(dom, cfg.size());

        Step[] stack = new Step[program.basicBlockCount() * 2];
        int head = 0;
        Step start = new Step(0);
        Arrays.fill(start.slotStates, -1);
        stack[head++] = start;

        while (head > 0) {
            Step step = stack[--head];

            int[] previousStates = step.slotStates;
            int[] states = previousStates.clone();

            IntObjectMap<BitSet> callSites = liveInInformation.get(step.node);
            IntObjectMap<BitSet> updatesByCallSite = new IntObjectOpenHashMap<>();
            int[] callSiteLocations = callSites.keys().toArray();
            Arrays.sort(callSiteLocations);
            for (int callSiteLocation : callSiteLocations) {
                BitSet liveIns = callSites.get(callSiteLocation);
                for (int liveVar = liveIns.nextSetBit(0); liveVar >= 0; liveVar = liveIns.nextSetBit(liveVar + 1)) {
                    int slot = colors[liveVar];
                    states[slot] = liveVar;
                }
                for (int slot = 0; slot < states.length; ++slot) {
                    if (!liveIns.get(slot)) {
                        states[slot] = -1;
                    }
                }

                updatesByCallSite.put(callSiteLocation, compareStates(previousStates, states, autoSpilled));
                previousStates = states;
            }

            for (int succ : domGraph.outgoingEdges(step.node)) {
                Step next = new Step(succ);
                System.arraycopy(states, 0, next.slotStates, 0, usedColors);
                stack[head++] = next;
            }
        }

        return slotsToUpdate;
    }

    private static BitSet compareStates(int[] oldStates, int[] newStates, boolean[] autoSpilled) {
        BitSet changedStates = new BitSet();

        for (int i = 0; i < oldStates.length; ++i) {
            if (oldStates[i] != newStates[i]) {
                changedStates.set(i);
            }
        }

        for (int i = 0; i < newStates.length; ++i) {
            if (autoSpilled[i]) {
                changedStates.clear(i);
            }
        }

        return changedStates;
    }

    private void putLiveInGcRoots(Program program, List<IntObjectMap<BitSet>> liveInInformation,
            List<IntObjectMap<BitSet>> updateInformation, int[] colors) {
        for (int i = 0; i < program.basicBlockCount(); ++i) {
            BasicBlock block = program.basicBlockAt(i);
            IntObjectMap<BitSet> liveInsByIndex = liveInInformation.get(i);
            IntObjectMap<BitSet> updatesByIndex = updateInformation.get(i);
            int[] callSiteLocations = liveInsByIndex.keys().toArray();
            Arrays.sort(callSiteLocations);
            for (int j = callSiteLocations.length - 1; j >= 0; --j) {
                int callSiteLocation = callSiteLocations[j];
                BitSet liveIns = liveInsByIndex.get(callSiteLocation);
                BitSet updates = updatesByIndex.get(callSiteLocation);
                if (updates.isEmpty()) {
                    storeLiveIns(block, j, liveIns, updates, colors);
                }
            }
        }
    }

    private void storeLiveIns(BasicBlock block, int index, BitSet liveIns, BitSet updates, int[] colors) {
        Program program = block.getProgram();
        List<Instruction> instructions = block.getInstructions();
        Instruction callInstruction = instructions.get(index);
        List<Instruction> instructionsToAdd = new ArrayList<>();

        for (int var = liveIns.nextSetBit(0); var >= 0; var = liveIns.nextSetBit(var + 1)) {
            int slot = colors[var];
            if (!updates.get(slot)) {
                continue;
            }

            Variable slotVar = program.createVariable();
            IntegerConstantInstruction slotConstant = new IntegerConstantInstruction();
            slotConstant.setReceiver(slotVar);
            slotConstant.setConstant(slot);
            slotConstant.setLocation(callInstruction.getLocation());
            instructionsToAdd.add(slotConstant);

            InvokeInstruction registerInvocation = new InvokeInstruction();
            registerInvocation.setType(InvocationType.SPECIAL);
            registerInvocation.setMethod(new MethodReference(Mutator.class, "registerGcRoot", int.class,
                    Object.class, void.class));
            registerInvocation.getArguments().add(slotVar);
            registerInvocation.getArguments().add(program.variableAt(var));
            instructionsToAdd.add(registerInvocation);
        }

        for (int slot = updates.nextSetBit(0); slot >= 0; slot = updates.nextSetBit(slot + 1)) {


            Variable slotVar = program.createVariable();
            IntegerConstantInstruction slotConstant = new IntegerConstantInstruction();
            slotConstant.setReceiver(slotVar);
            slotConstant.setConstant(slot++);
            slotConstant.setLocation(callInstruction.getLocation());
            instructionsToAdd.add(slotConstant);

            InvokeInstruction clearInvocation = new InvokeInstruction();
            clearInvocation.setType(InvocationType.SPECIAL);
            clearInvocation.setMethod(new MethodReference(Mutator.class, "removeGcRoot", int.class, void.class));
            clearInvocation.getArguments().add(slotVar);
            clearInvocation.setLocation(callInstruction.getLocation());
            instructionsToAdd.add(clearInvocation);
        }

        instructions.addAll(index, instructionsToAdd);
    }

    private void addStackAllocation(Program program, int maxDepth) {
        BasicBlock block = program.basicBlockAt(0);
        List<Instruction> instructionsToAdd = new ArrayList<>();
        Variable sizeVariable = program.createVariable();

        IntegerConstantInstruction sizeConstant = new IntegerConstantInstruction();
        sizeConstant.setReceiver(sizeVariable);
        sizeConstant.setConstant(maxDepth);
        instructionsToAdd.add(sizeConstant);

        InvokeInstruction invocation = new InvokeInstruction();
        invocation.setType(InvocationType.SPECIAL);
        invocation.setMethod(new MethodReference(Mutator.class, "allocStack", int.class, void.class));
        invocation.getArguments().add(sizeVariable);
        instructionsToAdd.add(invocation);

        block.getInstructions().addAll(0, instructionsToAdd);
    }

    private void addStackRelease(Program program, int maxDepth) {
        List<BasicBlock> blocks = new ArrayList<>();
        boolean hasResult = false;
        for (int i = 0; i < program.basicBlockCount(); ++i) {
            BasicBlock block = program.basicBlockAt(i);
            Instruction instruction = block.getLastInstruction();
            if (instruction instanceof ExitInstruction) {
                blocks.add(block);
                if (((ExitInstruction) instruction).getValueToReturn() != null) {
                    hasResult = true;
                }
            }
        }

        BasicBlock exitBlock;
        if (blocks.size() == 1) {
            exitBlock = blocks.get(0);
        } else {
            exitBlock = program.createBasicBlock();
            ExitInstruction exit = new ExitInstruction();
            exitBlock.getInstructions().add(exit);

            if (hasResult) {
                Phi phi = new Phi();
                phi.setReceiver(program.createVariable());
                exitBlock.getPhis().add(phi);
                exit.setValueToReturn(phi.getReceiver());

                for (BasicBlock block : blocks) {
                    ExitInstruction oldExit = (ExitInstruction) block.getLastInstruction();
                    Incoming incoming = new Incoming();
                    incoming.setSource(block);
                    incoming.setValue(oldExit.getValueToReturn());
                    phi.getIncomings().add(incoming);

                    JumpInstruction jumpToExit = new JumpInstruction();
                    jumpToExit.setTarget(exitBlock);
                    jumpToExit.setLocation(oldExit.getLocation());

                    block.getInstructions().set(block.getInstructions().size() - 1, jumpToExit);
                }
            }
        }

        List<Instruction> instructionsToAdd = new ArrayList<>();
        Variable sizeVariable = program.createVariable();

        IntegerConstantInstruction sizeConstant = new IntegerConstantInstruction();
        sizeConstant.setReceiver(sizeVariable);
        sizeConstant.setConstant(maxDepth);
        instructionsToAdd.add(sizeConstant);

        InvokeInstruction invocation = new InvokeInstruction();
        invocation.setType(InvocationType.SPECIAL);
        invocation.setMethod(new MethodReference(Mutator.class, "releaseStack", int.class, void.class));
        invocation.getArguments().add(sizeVariable);
        instructionsToAdd.add(invocation);

        exitBlock.getInstructions().addAll(exitBlock.getInstructions().size() - 1, instructionsToAdd);
    }

    private boolean isReference(TypeInferer typeInferer, int var) {
        VariableType liveType = typeInferer.typeOf(var);
        switch (liveType) {
            case BYTE_ARRAY:
            case CHAR_ARRAY:
            case SHORT_ARRAY:
            case INT_ARRAY:
            case FLOAT_ARRAY:
            case LONG_ARRAY:
            case DOUBLE_ARRAY:
            case OBJECT_ARRAY:
            case OBJECT:
                return true;
            default:
                return false;
        }
    }

    private boolean requiresGc(MethodReference methodReference) {
        ClassReader cls = classSource.get(methodReference.getClassName());
        if (cls == null) {
            return true;
        }
        if (cls.getAnnotations().get(NoGC.class.getName()) != null) {
            return false;
        }
        MethodReader method = cls.getMethod(methodReference.getDescriptor());
        return method.getAnnotations().get(NoGC.class.getName()) == null;
    }
}
