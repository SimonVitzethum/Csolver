; ModuleID = 'tests/dwarf-corpus/d_types.d'
source_filename = "tests/dwarf-corpus/d_types.d"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%0 = type { i32, i32, i64, [1 x ptr], [8 x i8] }
%d_types.Node = type { ptr, ptr, i64 }
%object.TypeInfo_Class = type { ptr, ptr, { i64, ptr }, { i64, ptr }, { i64, ptr }, { i64, ptr }, ptr, ptr, ptr, i16, i16, [4 x i8], ptr, { i64, ptr }, ptr, ptr, [4 x i32] }
%d_types.Pair = type { i64, i64 }
%object.Object = type { ptr, ptr }

@_D7d_types4Node6__initZ = constant %d_types.Node { ptr @_D7d_types4Node6__vtblZ, ptr null, i64 0 }, align 8 ; [#uses = 1]
@_D7d_types4Node6__vtblZ = constant [5 x ptr] [ptr @_D7d_types4Node7__ClassZ, ptr @_D6object6Object8toStringMFZAya, ptr @_D6object6Object6toHashMFNbNeZm, ptr @_D6object6Object5opCmpMFCQqZi, ptr @_D6object6Object8opEqualsMFCQtZb] ; [#uses = 2]
@_D7d_types4Node7__ClassZ = global %object.TypeInfo_Class { ptr @_D14TypeInfo_Class6__vtblZ, ptr null, { i64, ptr } { i64 24, ptr @_D7d_types4Node6__initZ }, { i64, ptr } { i64 12, ptr @.str }, { i64, ptr } { i64 5, ptr @_D7d_types4Node6__vtblZ }, { i64, ptr } zeroinitializer, ptr @_D6Object7__ClassZ, ptr null, ptr null, i16 566, i16 2, [4 x i8] zeroinitializer, ptr null, { i64, ptr } zeroinitializer, ptr null, ptr null, [4 x i32] [i32 -1299823565, i32 1878243906, i32 986990594, i32 -2042713432] } ; [#uses = 2]
@_D14TypeInfo_Class6__vtblZ = external constant [21 x ptr] ; [#uses = 1]
@.str = private unnamed_addr constant [13 x i8] c"d_types.Node\00" ; [#uses = 1]
@_D6Object7__ClassZ = external global %object.TypeInfo_Class ; [#uses = 1]
@_D7d_types12__ModuleInfoZ = global %0 { i32 -2147481596, i32 0, i64 1, [1 x ptr] [ptr @_D7d_types4Node7__ClassZ], [8 x i8] c"d_types\00" } ; [#uses = 1]
@_D7d_types11__moduleRefZ = linkonce_odr hidden global ptr @_D7d_types12__ModuleInfoZ, section "__minfo" ; [#uses = 1]
@llvm.used = appending global [1 x ptr] [ptr @_D7d_types11__moduleRefZ], section "llvm.metadata" ; [#uses = 0]

; [#uses = 0] [display name = sum_pair]
; Function Attrs: uwtable
define i64 @sum_pair(ptr %p_arg) #0 !dbg !12 {
  %p = alloca ptr, align 8                        ; [#uses = 3, size/byte = 8]
  store ptr %p_arg, ptr %p, align 8, !dbg !23     ; [debug line = tests/dwarf-corpus/d_types.d:2:16]
    #dbg_declare(ptr %p, !22, !DIExpression(), !24)
  %1 = load ptr, ptr %p, align 8, !dbg !25        ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:3:5]
  %2 = getelementptr inbounds %d_types.Pair, ptr %1, i32 0, i32 0 ; [#uses = 1, type = ptr]
  %3 = load i64, ptr %2, align 8, !dbg !25        ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:3:5]
  %4 = load ptr, ptr %p, align 8, !dbg !25        ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:3:5]
  %5 = getelementptr inbounds %d_types.Pair, ptr %4, i32 0, i32 1 ; [#uses = 1, type = ptr]
  %6 = load i64, ptr %5, align 8, !dbg !25        ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:3:5]
  %7 = add i64 %3, %6, !dbg !25                   ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:3:5]
  ret i64 %7, !dbg !25                            ; [debug line = tests/dwarf-corpus/d_types.d:3:5]
}

; [#uses = 1]
declare { i64, ptr } @_D6object6Object8toStringMFZAya(ptr nonnull) #1

; [#uses = 1]
declare i64 @_D6object6Object6toHashMFNbNeZm(ptr nonnull) #1

; [#uses = 1]
declare i32 @_D6object6Object5opCmpMFCQqZi(ptr nonnull, ptr) #1

; [#uses = 1]
declare zeroext i1 @_D6object6Object8opEqualsMFCQtZb(ptr nonnull, ptr) #1

; [#uses = 0] [display name = node_val]
; Function Attrs: uwtable
define i64 @node_val(ptr %n_arg) #0 !dbg !26 {
  %n = alloca ptr, align 8                        ; [#uses = 2, size/byte = 8]
  store ptr %n_arg, ptr %n, align 8, !dbg !38     ; [debug line = tests/dwarf-corpus/d_types.d:6:16]
    #dbg_declare(ptr %n, !37, !DIExpression(), !39)
  %1 = load ptr, ptr %n, align 8, !dbg !40        ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:7:5]
  %2 = getelementptr inbounds %d_types.Node, ptr %1, i32 0, i32 2 ; [#uses = 2, type = ptr]
  %3 = load i64, ptr %2, align 8, !dbg !40        ; [#uses = 0] [debug line = tests/dwarf-corpus/d_types.d:7:5]
  %4 = load i64, ptr %2, align 8, !dbg !40        ; [#uses = 1] [debug line = tests/dwarf-corpus/d_types.d:7:5]
  ret i64 %4, !dbg !40                            ; [debug line = tests/dwarf-corpus/d_types.d:7:5]
}

attributes #0 = { uwtable "frame-pointer"="all" "target-cpu"="x86-64" "target-features"="+cx16" }
attributes #1 = { "target-cpu"="x86-64" "target-features"="+cx16" }

!llvm.module.flags = !{!0}
!llvm.dbg.cu = !{!1}
!llvm.ldc.typeinfo._D7d_types4Node7__ClassZ = !{!8}
!llvm.ldc.classinfo._D7d_types4Node7__ClassZ = !{!9}
!llvm.ldc.typeinfo._D6Object7__ClassZ = !{!8}
!llvm.ldc.classinfo._D6Object7__ClassZ = !{!10}
!llvm.ident = !{!11}

!0 = !{i32 2, !"Debug Info Version", i32 3}
!1 = distinct !DICompileUnit(language: DW_LANG_D, file: !2, producer: "LDC 1.42.0 (LLVM 21.1.8)", isOptimized: false, runtimeVersion: 1, emissionKind: FullDebug, imports: !3)
!2 = !DIFile(filename: "tests/dwarf-corpus/d_types.d", directory: "/home/simon/Schreibtisch/CSolver")
!3 = !{!4}
!4 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !5, entity: !6, file: !2)
!5 = !DIModule(scope: !2, name: "d_types")
!6 = !DIModule(scope: !7, name: "object")
!7 = !DIFile(filename: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/ldc2-1.42.0-linux-x86_64/bin/../import/object.d", directory: "")
!8 = !{ptr undef}
!9 = !{%d_types.Node undef, i1 false}
!10 = !{%object.Object undef, i1 false}
!11 = !{!"ldc version 1.42.0"}
!12 = distinct !DISubprogram(name: "sum_pair", linkageName: "sum_pair", scope: !5, file: !2, line: 2, type: !13, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !1, retainedNodes: !21)
!13 = !DISubroutineType(types: !14)
!14 = !{!15, !16}
!15 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!16 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "d_types.Pair*", baseType: !17, size: 64)
!17 = !DICompositeType(tag: DW_TAG_structure_type, name: "Pair", scope: !5, file: !2, line: 1, size: 128, align: 64, elements: !18, identifier: "S7d_types4Pair")
!18 = !{!19, !20}
!19 = !DIDerivedType(tag: DW_TAG_member, name: "a", file: !2, line: 1, baseType: !15, size: 64, align: 64, flags: DIFlagPublic)
!20 = !DIDerivedType(tag: DW_TAG_member, name: "b", file: !2, line: 1, baseType: !15, size: 64, align: 64, offset: 64, flags: DIFlagPublic)
!21 = !{!22}
!22 = !DILocalVariable(name: "p", arg: 1, scope: !12, file: !2, line: 2, type: !16)
!23 = !DILocation(line: 2, column: 16, scope: !12)
!24 = !DILocation(line: 2, column: 29, scope: !12)
!25 = !DILocation(line: 3, column: 5, scope: !12)
!26 = distinct !DISubprogram(name: "node_val", linkageName: "node_val", scope: !5, file: !2, line: 6, type: !27, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !1, retainedNodes: !36)
!27 = !DISubroutineType(types: !28)
!28 = !{!15, !29}
!29 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "d_types.Node*", baseType: !30, size: 64)
!30 = !DICompositeType(tag: DW_TAG_class_type, name: "Node", scope: !5, file: !2, line: 5, baseType: !31, size: 192, align: 64, elements: !33, identifier: "C7d_types4Node")
!31 = !DICompositeType(tag: DW_TAG_class_type, name: "Object", scope: !6, file: !7, line: 140, size: 128, align: 64, elements: !32, identifier: "C6Object")
!32 = !{}
!33 = !{!34, !35}
!34 = !DIDerivedType(tag: DW_TAG_inheritance, scope: !30, baseType: !31, flags: DIFlagPublic, extraData: i32 0)
!35 = !DIDerivedType(tag: DW_TAG_member, name: "v", file: !2, line: 5, baseType: !15, size: 64, align: 64, offset: 128, flags: DIFlagPublic)
!36 = !{!37}
!37 = !DILocalVariable(name: "n", arg: 1, scope: !26, file: !2, line: 6, type: !29)
!38 = !DILocation(line: 6, column: 16, scope: !26)
!39 = !DILocation(line: 6, column: 30, scope: !26)
!40 = !DILocation(line: 7, column: 5, scope: !26)
