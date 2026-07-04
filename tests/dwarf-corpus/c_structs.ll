; ModuleID = 'tests/dwarf-corpus/c_structs.c'
source_filename = "tests/dwarf-corpus/c_structs.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: read) uwtable
define dso_local i64 @sum_pair(ptr noundef readonly captures(none) %0) local_unnamed_addr #0 !dbg !14 {
    #dbg_value(ptr %0, !29, !DIExpression(), !30)
  %2 = load i64, ptr %0, align 8, !dbg !31, !tbaa !32
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 8, !dbg !35
  %4 = load i64, ptr %3, align 8, !dbg !35, !tbaa !36
  %5 = add nsw i64 %4, %2, !dbg !37
  ret i64 %5, !dbg !38
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(read, inaccessiblemem: none, target_mem0: none, target_mem1: none) uwtable
define dso_local i32 @read_member(ptr noundef readonly captures(none) %0) local_unnamed_addr #1 !dbg !39 {
    #dbg_value(ptr %0, !53, !DIExpression(), !54)
  %2 = getelementptr inbounds nuw i8, ptr %0, i64 8, !dbg !55
  %3 = load ptr, ptr %2, align 8, !dbg !55, !tbaa !56
  %4 = load i32, ptr %3, align 4, !dbg !60, !tbaa !10
  ret i32 %4, !dbg !61
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: read) uwtable
define dso_local i64 @second(ptr noundef readonly captures(none) %0) local_unnamed_addr #0 !dbg !62 {
    #dbg_value(ptr %0, !64, !DIExpression(), !65)
  %2 = getelementptr inbounds nuw i8, ptr %0, i64 8, !dbg !66
  %3 = load i64, ptr %2, align 8, !dbg !67, !tbaa !36
  ret i64 %3, !dbg !68
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: read) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(read, inaccessiblemem: none, target_mem0: none, target_mem1: none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}
!llvm.errno.tbaa = !{!10}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "clang version 22.1.6", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "tests/dwarf-corpus/c_structs.c", directory: "/home/simon/Schreibtisch/CSolver", checksumkind: CSK_MD5, checksum: "5c808052e44511ba612baee42d7b6127")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"debug-info-assignment-tracking", i1 true}
!9 = !{!"clang version 22.1.6"}
!10 = !{!11, !11, i64 0}
!11 = !{!"int", !12, i64 0}
!12 = !{!"omnipotent char", !13, i64 0}
!13 = !{!"Simple C/C++ TBAA"}
!14 = distinct !DISubprogram(name: "sum_pair", scope: !1, file: !1, line: 8, type: !15, scopeLine: 8, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !28, keyInstructions: true)
!15 = !DISubroutineType(types: !16)
!16 = !{!17, !22}
!17 = !DIDerivedType(tag: DW_TAG_typedef, name: "int64_t", file: !18, line: 27, baseType: !19)
!18 = !DIFile(filename: "/usr/include/bits/stdint-intn.h", directory: "", checksumkind: CSK_MD5, checksum: "10d5fe006d042c979d10252beb26dc83")
!19 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int64_t", file: !20, line: 44, baseType: !21)
!20 = !DIFile(filename: "/usr/include/bits/types.h", directory: "", checksumkind: CSK_MD5, checksum: "bcb6d4a34cad6d89d16a897638e8f5b7")
!21 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!22 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !23, size: 64)
!23 = !DIDerivedType(tag: DW_TAG_typedef, name: "Pair", file: !1, line: 5, baseType: !24)
!24 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !1, line: 5, size: 128, elements: !25)
!25 = !{!26, !27}
!26 = !DIDerivedType(tag: DW_TAG_member, name: "a", scope: !24, file: !1, line: 5, baseType: !17, size: 64)
!27 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !24, file: !1, line: 5, baseType: !17, size: 64, offset: 64)
!28 = !{!29}
!29 = !DILocalVariable(name: "p", arg: 1, scope: !14, file: !1, line: 8, type: !22)
!30 = !DILocation(line: 0, scope: !14)
!31 = !DILocation(line: 9, column: 15, scope: !14)
!32 = !{!33, !34, i64 0}
!33 = !{!"", !34, i64 0, !34, i64 8}
!34 = !{!"long", !12, i64 0}
!35 = !DILocation(line: 9, column: 22, scope: !14)
!36 = !{!33, !34, i64 8}
!37 = !DILocation(line: 9, column: 17, scope: !14, atomGroup: 1, atomRank: 2)
!38 = !DILocation(line: 9, column: 5, scope: !14, atomGroup: 1, atomRank: 1)
!39 = distinct !DISubprogram(name: "read_member", scope: !1, file: !1, line: 15, type: !40, scopeLine: 15, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !52, keyInstructions: true)
!40 = !DISubroutineType(types: !41)
!41 = !{!42, !45}
!42 = !DIDerivedType(tag: DW_TAG_typedef, name: "int32_t", file: !18, line: 26, baseType: !43)
!43 = !DIDerivedType(tag: DW_TAG_typedef, name: "__int32_t", file: !20, line: 41, baseType: !44)
!44 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!45 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !46, size: 64)
!46 = !DIDerivedType(tag: DW_TAG_typedef, name: "Wrap", file: !1, line: 12, baseType: !47)
!47 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !1, line: 12, size: 128, elements: !48)
!48 = !{!49, !50}
!49 = !DIDerivedType(tag: DW_TAG_member, name: "tag", scope: !47, file: !1, line: 12, baseType: !17, size: 64)
!50 = !DIDerivedType(tag: DW_TAG_member, name: "data", scope: !47, file: !1, line: 12, baseType: !51, size: 64, offset: 64)
!51 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !42, size: 64)
!52 = !{!53}
!53 = !DILocalVariable(name: "w", arg: 1, scope: !39, file: !1, line: 15, type: !45)
!54 = !DILocation(line: 0, scope: !39)
!55 = !DILocation(line: 16, column: 17, scope: !39)
!56 = !{!57, !58, i64 8}
!57 = !{!"", !34, i64 0, !58, i64 8}
!58 = !{!"p1 int", !59, i64 0}
!59 = !{!"any pointer", !12, i64 0}
!60 = !DILocation(line: 16, column: 12, scope: !39, atomGroup: 1, atomRank: 2)
!61 = !DILocation(line: 16, column: 5, scope: !39, atomGroup: 1, atomRank: 1)
!62 = distinct !DISubprogram(name: "second", scope: !1, file: !1, line: 20, type: !15, scopeLine: 20, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !63, keyInstructions: true)
!63 = !{!64}
!64 = !DILocalVariable(name: "p", arg: 1, scope: !62, file: !1, line: 20, type: !22)
!65 = !DILocation(line: 0, scope: !62)
!66 = !DILocation(line: 21, column: 15, scope: !62)
!67 = !DILocation(line: 21, column: 15, scope: !62, atomGroup: 1, atomRank: 2)
!68 = !DILocation(line: 21, column: 5, scope: !62, atomGroup: 1, atomRank: 1)
