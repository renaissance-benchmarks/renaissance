/*
 * Copyright 2016-2020 chronicle.software
 *
 *       https://chronicle.software
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package net.openhft.chronicle.core.internal.cleaner;

import net.openhft.chronicle.core.Jvm;
import net.openhft.chronicle.core.cleaner.spi.ByteBufferCleanerService;
import net.openhft.chronicle.core.internal.util.DirectBufferUtil;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.nio.ByteBuffer;
import java.util.logging.Level;
import java.util.logging.Logger;

public final class ReflectionBasedByteBufferCleanerService implements ByteBufferCleanerService {
    private static final MethodHandle CLEANER_METHOD;
    private static final MethodHandle CLEAN_METHOD;
    private static final Impact IMPACT;

    static {
        //
        // The code below makes the following assumptions:
        //
        // - The internal DirectByteBuffer class implements the (internal) DirectBuffer interface.
        // - The DirectBuffer interface provides a 'cleaner()' method that returns an instance of
        //   some Cleaner-like class or interface of unknown type, such as sun.misc.Cleaner (until
        //   JDK 8), jdk.internal.ref.Cleaner (until JDK 25) or sun.nio.Cleaner (since JDK 26).
        // - The Cleaner-like instance provides a 'clean()' method that can be used to trigger
        //   cleanup of a DirectByteBuffer instance.
        //
        // So far the above appears to hold for OpenJDK versions from 7 to 26.
        //
        final MethodHandles.Lookup lookup = MethodHandles.lookup();
        MethodHandle cleaner = null;
        MethodHandle clean = null;
        Impact impact = Impact.SOME_IMPACT;
        try {
            cleaner = lookup.unreflect(DirectBufferUtil.directBufferClass().getDeclaredMethod("cleaner"));
            clean = lookup.findVirtual(cleaner.type().returnType(), "clean", MethodType.methodType(void.class));
        } catch (NoSuchMethodException | IllegalAccessException e) {
            // Don't want to record this in tests so just send to slf4j
            final Logger logger = Logger.getLogger(ReflectionBasedByteBufferCleanerService.class.getName());
            if (logger.isLoggable(Level.WARNING)) {
                Logger.getLogger(ReflectionBasedByteBufferCleanerService.class.getName())
                        .warning("Make sure to --add-exports to enable " + ReflectionBasedByteBufferCleanerService.class.getSimpleName());
            }
            impact = Impact.UNAVAILABLE;
        }
        CLEAN_METHOD = clean;
        CLEANER_METHOD = cleaner;
        IMPACT = impact;
    }

    @Override
    public void clean(final ByteBuffer buffer) {
        if (IMPACT == Impact.UNAVAILABLE) {
            // There might not be a cleaner after all.
            // See https://github.com/OpenHFT/Chronicle-Core/issues/140
            Logger.getLogger(ReflectionBasedByteBufferCleanerService.class.getName())
                    .warning("Cleaning is not available. The ByteBuffer 0x" + Integer.toHexString(System.identityHashCode(buffer)) +
                            " could not be explicitly cleaned and will thus linger until the next GC.");
        } else {
            try {
                final Object cleaner = CLEANER_METHOD.invoke(DirectBufferUtil.directBufferClass().cast(buffer));
                CLEAN_METHOD.invoke(cleaner);
            } catch (Throwable throwable) {
                throw Jvm.rethrow(throwable);
            }
        }
    }

    @Override
    public Impact impact() {
        return IMPACT;
    }
}
