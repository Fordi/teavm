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
package org.teavm.runtime;

import org.teavm.interop.Address;
import org.teavm.interop.NoGC;

@NoGC
public final class Mutator {
    private Mutator() {
    }

    public static native void allocStack(int size);

    public static native void registerGcRoot(int index, Object object);

    public static native void removeGcRoot(int index);

    public static native void releaseStack(int size);

    public static native Address getStaticGcRoots();

    public static native Address getStackGcRoots();

    public static native Address getNextStackRoots(Address address);

    public static native int getStackRootCount(Address address);

    public static native Address getStackRootPointer(Address address);
}
