; ModuleID = 'tests/dwarf-corpus/objc_ptrs.m'
source_filename = "tests/dwarf-corpus/objc_ptrs.m"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: read) uwtable
define dso_local i64 @sum_pair(ptr noundef readonly captures(none) %0) local_unnamed_addr #0 !dbg !14 {
    #dbg_value(ptr %0, !24, !DIExpression(), !25)
  %2 = load i64, ptr %0, align 8, !dbg !26, !tbaa !27
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 8, !dbg !30
  %4 = load i64, ptr %3, align 8, !dbg !30, !tbaa !31
  %5 = add nsw i64 %4, %2, !dbg !32
  ret i64 %5, !dbg !33
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: read) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}
!llvm.errno.tbaa = !{!10}

!0 = distinct !DICompileUnit(language: DW_LANG_ObjC, file: !1, producer: "clang version 22.1.6", isOptimized: true, runtimeVersion: 1, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "tests/dwarf-corpus/objc_ptrs.m", directory: "/home/simon/Schreibtisch/CSolver", checksumkind: CSK_MD5, checksum: "556ce1974854aefbc8de15cef15bcef0")
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
!14 = distinct !DISubprogram(name: "sum_pair", scope: !1, file: !1, line: 4, type: !15, scopeLine: 4, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !23)
!15 = !DISubroutineType(types: !16)
!16 = !{!17, !18}
!17 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!18 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !19, size: 64)
!19 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "Pair", file: !1, line: 3, size: 128, elements: !20)
!20 = !{!21, !22}
!21 = !DIDerivedType(tag: DW_TAG_member, name: "a", scope: !19, file: !1, line: 3, baseType: !17, size: 64)
!22 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !19, file: !1, line: 3, baseType: !17, size: 64, offset: 64)
!23 = !{!24}
!24 = !DILocalVariable(name: "p", arg: 1, scope: !14, file: !1, line: 4, type: !18)
!25 = !DILocation(line: 0, scope: !14)
!26 = !DILocation(line: 4, column: 43, scope: !14)
!27 = !{!28, !29, i64 0}
!28 = !{!"Pair", !29, i64 0, !29, i64 8}
!29 = !{!"long", !12, i64 0}
!30 = !DILocation(line: 4, column: 50, scope: !14)
!31 = !{!28, !29, i64 8}
!32 = !DILocation(line: 4, column: 45, scope: !14)
!33 = !DILocation(line: 4, column: 33, scope: !14)
