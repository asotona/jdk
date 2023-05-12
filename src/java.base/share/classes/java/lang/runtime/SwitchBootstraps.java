/*
 * Copyright (c) 2017, 2021, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package java.lang.runtime;

import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import static java.lang.constant.ConstantDescs.*;
import java.lang.constant.MethodTypeDesc;
import java.lang.invoke.CallSite;
import java.lang.invoke.ConstantBootstraps;
import java.lang.invoke.ConstantCallSite;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.util.stream.Stream;

import jdk.internal.classfile.Classfile;
import jdk.internal.javac.PreviewFeature;

import java.lang.invoke.LambdaConversionException;
import static java.lang.invoke.MethodHandles.Lookup.ClassOption.NESTMATE;
import static java.lang.invoke.MethodHandles.Lookup.ClassOption.STRONG;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;
import static java.util.Objects.requireNonNull;
import static jdk.internal.classfile.Classfile.*;
import jdk.internal.classfile.instruction.SwitchCase;

/**
 * Bootstrap methods for linking {@code invokedynamic} call sites that implement
 * the selection functionality of the {@code switch} statement.  The bootstraps
 * take additional static arguments corresponding to the {@code case} labels
 * of the {@code switch}, implicitly numbered sequentially from {@code [0..N)}.
 *
 * @since 17
 */
@PreviewFeature(feature=PreviewFeature.Feature.SWITCH_PATTERN_MATCHING)
public class SwitchBootstraps {

    private SwitchBootstraps() {}

    private static final MethodHandles.Lookup LOOKUP = MethodHandles.lookup();

    private static final MethodHandle DO_TYPE_SWITCH;
    private static final MethodHandle DO_ENUM_SWITCH;

    private static final MethodType DO_TYPE_SWITCH_TYPE = MethodType.methodType(
                                           int.class, Object.class, int.class, Object[].class);
    private static final MethodType GENERATED_SWITCH_TYPE = MethodType.methodType(
                                           int.class, Object.class, int.class);
    private static final MethodTypeDesc MTD_GENERATED_SWITCH = GENERATED_SWITCH_TYPE.describeConstable().get();

    static {
        try {
            DO_TYPE_SWITCH = LOOKUP.findStatic(SwitchBootstraps.class, "doTypeSwitch",
                                           DO_TYPE_SWITCH_TYPE);
            DO_ENUM_SWITCH = LOOKUP.findStatic(SwitchBootstraps.class, "doEnumSwitch",
                                           MethodType.methodType(int.class, Enum.class, int.class, Object[].class));
        }
        catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    /**
     * Bootstrap method for linking an {@code invokedynamic} call site that
     * implements a {@code switch} on a target of a reference type.  The static
     * arguments are an array of case labels which must be non-null and of type
     * {@code String} or {@code Integer} or {@code Class}.
     * <p>
     * The type of the returned {@code CallSite}'s method handle will have
     * a return type of {@code int}.   It has two parameters: the first argument
     * will be an {@code Object} instance ({@code target}) and the second
     * will be {@code int} ({@code restart}).
     * <p>
     * If the {@code target} is {@code null}, then the method of the call site
     * returns {@literal -1}.
     * <p>
     * If the {@code target} is not {@code null}, then the method of the call site
     * returns the index of the first element in the {@code labels} array starting from
     * the {@code restart} index matching one of the following conditions:
     * <ul>
     *   <li>the element is of type {@code Class} that is assignable
     *       from the target's class; or</li>
     *   <li>the element is of type {@code String} or {@code Integer} and
     *       equals to the target.</li>
     * </ul>
     * <p>
     * If no element in the {@code labels} array matches the target, then
     * the method of the call site return the length of the {@code labels} array.
     *
     * @param lookup Represents a lookup context with the accessibility
     *               privileges of the caller.  When used with {@code invokedynamic},
     *               this is stacked automatically by the VM.
     * @param invocationName unused
     * @param invocationType The invocation type of the {@code CallSite} with two parameters,
     *                       a reference type, an {@code int}, and {@code int} as a return type.
     * @param labels case labels - {@code String} and {@code Integer} constants
     *               and {@code Class} instances, in any combination
     * @return a {@code CallSite} returning the first matching element as described above
     *
     * @throws NullPointerException if any argument is {@code null}
     * @throws IllegalArgumentException if any element in the labels array is null, if the
     * invocation type is not not a method type of first parameter of a reference type,
     * second parameter of type {@code int} and with {@code int} as its return type,
     * or if {@code labels} contains an element that is not of type {@code String},
     * {@code Integer} or {@code Class}.
     * @jvms 4.4.6 The CONSTANT_NameAndType_info Structure
     * @jvms 4.4.10 The CONSTANT_Dynamic_info and CONSTANT_InvokeDynamic_info Structures
     */
    public static CallSite typeSwitch(MethodHandles.Lookup lookup,
                                      String invocationName,
                                      MethodType invocationType,
                                      Object... labels) {
        if (invocationType.parameterCount() != 2
            || (!invocationType.returnType().equals(int.class))
            || invocationType.parameterType(0).isPrimitive()
            || !invocationType.parameterType(1).equals(int.class))
            throw new IllegalArgumentException("Illegal invocation type " + invocationType);
        requireNonNull(labels);

        labels = labels.clone();
        Stream.of(labels).forEach(SwitchBootstraps::verifyLabel);

        boolean hasOnlyClassLabels = Stream.of(labels).allMatch(l -> l instanceof Class<?>);
        MethodHandle target;

        if (hasOnlyClassLabels) {
            try {
                target = lookup.findStatic(generateInnerClass(lookup, labels), "typeSwitch", MethodType.methodType(int.class, Object.class, int.class));
            } catch (LambdaConversionException | NoSuchMethodException | IllegalAccessException ex) {
                throw new IllegalStateException(ex);
            }
        } else {
            target = MethodHandles.insertArguments(DO_TYPE_SWITCH, 2, (Object) labels);
        }

        return new ConstantCallSite(target);
    }

   @SuppressWarnings("removal")
    private static Class<?> generateInnerClass(MethodHandles.Lookup caller, Object[] labels) throws LambdaConversionException {
        Map<Integer, Class<?>> hashMap = new HashMap<>();
        Map<Class<?>, BitSet> possitionsMap = new HashMap<>();
        for (int i = 0; i < labels.length; i++) {
            var cls = (Class<?>)labels[i];
            var sub = cls.getPermittedSubclasses();
            if (sub != null || (cls.getModifiers() & ACC_FINAL) != 0) {
                hashMap.put(cls.hashCode(), cls);
                possitionsMap.computeIfAbsent(cls, c -> new BitSet()).set(i);
            }
            if (sub != null) for (var sc : sub) {
                hashMap.put(sc.hashCode(), sc);
                possitionsMap.computeIfAbsent(sc, c -> new BitSet()).set(i);
            }
        }
        //lookupSwitch (arg0.getClass().hash()) {
        //    case #1 -> if (arg0 instanceof labelWith#1) {
        //                  if (arg1 <= labelBitset#1) return #1
        //                  else if (arg1 <= labelBitset#2) return #2
        //                  else return labels.length;
        //              } else return fallback();
        //    default -> return fallback();
        //
        //fallback
        //tableSwitch (arg1) {
        //    case 0 -> if (arg0 instanceof label0) return 0; //fallthrough else
        //    case 1 -> //fallthrough for labels handled in lookupswith
        //    case 2 -> if (arg0 instanceof label2) return 2; //fallthrough else
        //    default -> return labels.length;
        final byte[] classBytes = Classfile.build(ClassDesc.of(caller.lookupClass().getPackageName(), "TypeSwitch"), clb -> clb
                .withFlags(ACC_SUPER | ACC_FINAL | ACC_SYNTHETIC)
                .withMethodBody("typeSwitch", MTD_GENERATED_SWITCH, ACC_PUBLIC | ACC_STATIC | ACC_FINAL, cob -> {
                    var cont = cob.newLabel();
                    cob.aload(0)
                       .if_nonnull(cont)
                       .iconst_m1()
                       .ireturn()
                       .labelBinding(cont);
                    var end = cob.newLabel();
                    if (labels.length > 0) {
                        var fallback = cob.newLabel();
                        var hashCases = new ArrayList<SwitchCase>(hashMap.size());
                        for (int hash : hashMap.keySet()) {
                            hashCases.add(SwitchCase.of(hash, cob.newLabel()));
                        }

                        //hash lookup
                        cob.aload(0)
                           .invokevirtual(CD_Object, "getClass", MethodTypeDesc.of(CD_Class))
                           .invokevirtual(CD_Class, "hashCode", MethodTypeDesc.of(CD_int))
                           .lookupswitch(fallback, hashCases);
                        for (var c : hashCases) {
                            var cls = hashMap.get(c.caseValue());
                            cob.labelBinding(c.target())
                               .aload(0)
                               .instanceof_(cls.describeConstable().get())
                               .ifeq(fallback);
                            var possitions = possitionsMap.get(cls);
                            for (int i = possitions.nextSetBit(0); i >= 0; i = possitions.nextSetBit(i+1)) {
                                var skip = cob.newLabel();
                                cob.iload(1)
                                   .constantInstruction(i)
                                   .if_icmpgt(i == possitions.length() - 1 ? end : skip)
                                   .constantInstruction(i)
                                   .ireturn()
                                   .labelBinding(skip);
                            }
                        }

                        //fallback
                        var fallbackCases = new ArrayList<SwitchCase>(labels.length);
                        for (int i = 0; i < labels.length; i++) {
                            fallbackCases.add(SwitchCase.of(i, cob.newLabel()));
                        }
                        cob.labelBinding(fallback)
                           .iload(1)
                           .tableswitch(0, labels.length - 1, end, fallbackCases);
                        for (var c : fallbackCases) {
                            var fallThrough = cob.newLabel();
                            cob.labelBinding(c.target())
                               .aload(0)
                               .instanceof_(((Class<?>)labels[c.caseValue()]).describeConstable().get())
                               .ifeq(fallThrough)
                               .constantInstruction(c.caseValue())
                               .ireturn()
                               .labelBinding(fallThrough);
                        }
                    }
                    cob.labelBinding(end)
                       .constantInstruction(labels.length)
                       .ireturn();
                }));
        try {
            // this class is linked at the indy callsite; so define a hidden nestmate
            MethodHandles.Lookup lookup;
            lookup = caller.defineHiddenClass(classBytes, true, NESTMATE, STRONG);
            return lookup.lookupClass();
        } catch (IllegalAccessException e) {
            throw new LambdaConversionException("Exception defining lambda proxy class", e);
        } catch (Throwable t) {
            throw new InternalError(t);
        }
    }

    private static void verifyLabel(Object label) {
        if (label == null) {
            throw new IllegalArgumentException("null label found");
        }
        Class<?> labelClass = label.getClass();
        if (labelClass != Class.class &&
            labelClass != String.class &&
            labelClass != Integer.class) {
            throw new IllegalArgumentException("label with illegal type found: " + label.getClass());
        }
    }

    private static int doTypeSwitch(Object target, int startIndex, Object[] labels) {
        if (target == null)
            return -1;

        // Dumbest possible strategy
        Class<?> targetClass = target.getClass();
        for (int i = startIndex; i < labels.length; i++) {
            Object label = labels[i];
            if (label instanceof Class<?> c) {
                if (c.isAssignableFrom(targetClass))
                    return i;
            } else if (label instanceof Integer constant) {
                if (target instanceof Number input && constant.intValue() == input.intValue()) {
                    return i;
                } else if (target instanceof Character input && constant.intValue() == input.charValue()) {
                    return i;
                }
            } else if (label.equals(target)) {
                return i;
            }
        }

        return labels.length;
    }

    /**
     * Bootstrap method for linking an {@code invokedynamic} call site that
     * implements a {@code switch} on a target of an enum type. The static
     * arguments are used to encode the case labels associated to the switch
     * construct, where each label can be encoded in two ways:
     * <ul>
     *   <li>as a {@code String} value, which represents the name of
     *       the enum constant associated with the label</li>
     *   <li>as a {@code Class} value, which represents the enum type
     *       associated with a type test pattern</li>
     * </ul>
     * <p>
     * The returned {@code CallSite}'s method handle will have
     * a return type of {@code int} and accepts two parameters: the first argument
     * will be an {@code Enum} instance ({@code target}) and the second
     * will be {@code int} ({@code restart}).
     * <p>
     * If the {@code target} is {@code null}, then the method of the call site
     * returns {@literal -1}.
     * <p>
     * If the {@code target} is not {@code null}, then the method of the call site
     * returns the index of the first element in the {@code labels} array starting from
     * the {@code restart} index matching one of the following conditions:
     * <ul>
     *   <li>the element is of type {@code Class} that is assignable
     *       from the target's class; or</li>
     *   <li>the element is of type {@code String} and equals to the target
     *       enum constant's {@link Enum#name()}.</li>
     * </ul>
     * <p>
     * If no element in the {@code labels} array matches the target, then
     * the method of the call site return the length of the {@code labels} array.
     *
     * @param lookup Represents a lookup context with the accessibility
     *               privileges of the caller. When used with {@code invokedynamic},
     *               this is stacked automatically by the VM.
     * @param invocationName unused
     * @param invocationType The invocation type of the {@code CallSite} with two parameters,
     *                       an enum type, an {@code int}, and {@code int} as a return type.
     * @param labels case labels - {@code String} constants and {@code Class} instances,
     *               in any combination
     * @return a {@code CallSite} returning the first matching element as described above
     *
     * @throws NullPointerException if any argument is {@code null}
     * @throws IllegalArgumentException if any element in the labels array is null, if the
     * invocation type is not a method type whose first parameter type is an enum type,
     * second parameter of type {@code int} and whose return type is {@code int},
     * or if {@code labels} contains an element that is not of type {@code String} or
     * {@code Class} of the target enum type.
     * @jvms 4.4.6 The CONSTANT_NameAndType_info Structure
     * @jvms 4.4.10 The CONSTANT_Dynamic_info and CONSTANT_InvokeDynamic_info Structures
     */
    public static CallSite enumSwitch(MethodHandles.Lookup lookup,
                                      String invocationName,
                                      MethodType invocationType,
                                      Object... labels) {
        if (invocationType.parameterCount() != 2
            || (!invocationType.returnType().equals(int.class))
            || invocationType.parameterType(0).isPrimitive()
            || !invocationType.parameterType(0).isEnum()
            || !invocationType.parameterType(1).equals(int.class))
            throw new IllegalArgumentException("Illegal invocation type " + invocationType);
        requireNonNull(labels);

        labels = labels.clone();

        Class<?> enumClass = invocationType.parameterType(0);
        labels = Stream.of(labels).map(l -> convertEnumConstants(lookup, enumClass, l)).toArray();

        MethodHandle target =
                MethodHandles.insertArguments(DO_ENUM_SWITCH, 2, (Object) labels);
        target = target.asType(invocationType);

        return new ConstantCallSite(target);
    }

    private static <E extends Enum<E>> Object convertEnumConstants(MethodHandles.Lookup lookup, Class<?> enumClassTemplate, Object label) {
        if (label == null) {
            throw new IllegalArgumentException("null label found");
        }
        Class<?> labelClass = label.getClass();
        if (labelClass == Class.class) {
            if (label != enumClassTemplate) {
                throw new IllegalArgumentException("the Class label: " + label +
                                                   ", expected the provided enum class: " + enumClassTemplate);
            }
            return label;
        } else if (labelClass == String.class) {
            @SuppressWarnings("unchecked")
            Class<E> enumClass = (Class<E>) enumClassTemplate;
            try {
                return ConstantBootstraps.enumConstant(lookup, (String) label, enumClass);
            } catch (IllegalArgumentException ex) {
                return null;
            }
        } else {
            throw new IllegalArgumentException("label with illegal type found: " + labelClass +
                                               ", expected label of type either String or Class");
        }
    }

    private static int doEnumSwitch(Enum<?> target, int startIndex, Object[] labels) {
        if (target == null)
            return -1;

        // Dumbest possible strategy
        Class<?> targetClass = target.getClass();
        for (int i = startIndex; i < labels.length; i++) {
            Object label = labels[i];
            if (label instanceof Class<?> c) {
                if (c.isAssignableFrom(targetClass))
                    return i;
            } else if (label == target) {
                return i;
            }
        }

        return labels.length;
    }

}
