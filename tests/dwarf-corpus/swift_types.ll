; ModuleID = '/tmp/swift_types.ll'
source_filename = "/tmp/swift_types.ll"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%swift.method_descriptor = type { i32, i32 }
%swift.type_descriptor = type opaque
%swift.vwtable = type { ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, i64, i64, i32, i32 }
%swift.type_metadata_record = type { i32 }
%swift.type = type { i64 }
%T11swift_types7CounterC = type <{ %swift.refcounted, %Ts5Int64V }>
%swift.refcounted = type { ptr, i64 }
%Ts5Int64V = type <{ i64 }>
%"$s11swift_types7CounterC1ns5Int64VvM.Frame" = type { [24 x i8] }
%T11swift_types4PairV = type <{ %Ts5Int64V, %Ts5Int64V }>
%swift.metadata_response = type { ptr, i64 }

@"\01l_entry_point" = private constant { i32, i32 } { i32 trunc (i64 sub (i64 ptrtoint (ptr @main to i64), i64 ptrtoint (ptr @"\01l_entry_point" to i64)) to i32), i32 0 }, section "swift5_entry", align 4
@"$s11swift_types7CounterC1ns5Int64VvpWvd" = hidden constant i64 16, align 8
@"$sBoWV" = external global ptr, align 8
@.str.11.swift_types = private constant [12 x i8] c"swift_types\00"
@"$s11swift_typesMXM" = linkonce_odr hidden constant <{ i32, i32, i32 }> <{ i32 0, i32 0, i32 trunc (i64 sub (i64 ptrtoint (ptr @.str.11.swift_types to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32 }>, ptr @"$s11swift_typesMXM", i32 0, i32 2) to i64)) to i32) }>, section ".rodata", no_sanitize_address, align 4
@.str.7.Counter = private constant [8 x i8] c"Counter\00"
@"$s11swift_types7CounterCMn" = hidden constant <{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }> <{ i32 -2147483568, i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_typesMXM" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }>, ptr @"$s11swift_types7CounterCMn", i32 0, i32 1) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @.str.7.Counter to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }>, ptr @"$s11swift_types7CounterCMn", i32 0, i32 2) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types7CounterCMa" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }>, ptr @"$s11swift_types7CounterCMn", i32 0, i32 3) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types7CounterCMF" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }>, ptr @"$s11swift_types7CounterCMn", i32 0, i32 4) to i64)) to i32), i32 0, i32 3, i32 9, i32 2, i32 1, i32 7, i32 8, i32 1, %swift.method_descriptor { i32 1, i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types7CounterCACycfC" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }>, ptr @"$s11swift_types7CounterCMn", i32 0, i32 13, i32 1) to i64)) to i32) } }>, section ".rodata", no_sanitize_address, align 4
@"$s11swift_types7CounterCMf" = internal global <{ ptr, ptr, ptr, i64, ptr, i32, i32, i32, i16, i16, i32, i32, ptr, ptr, i64, ptr }> <{ ptr null, ptr @"$s11swift_types7CounterCfD", ptr @"$sBoWV", i64 0, ptr null, i32 2, i32 0, i32 24, i16 7, i16 0, i32 96, i32 24, ptr @"$s11swift_types7CounterCMn", ptr null, i64 16, ptr @"$s11swift_types7CounterCACycfC" }>, align 8
@"symbolic _____ 11swift_types7CounterC" = linkonce_odr hidden constant <{ i8, i32, i8 }> <{ i8 1, i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types7CounterCMn" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i8, i32, i8 }>, ptr @"symbolic _____ 11swift_types7CounterC", i32 0, i32 1) to i64)) to i32), i8 0 }>, section "swift5_typeref", no_sanitize_address, align 2
@"$ss5Int64VMn" = external global %swift.type_descriptor, align 4
@"got.$ss5Int64VMn" = linkonce_odr hidden constant ptr @"$ss5Int64VMn"
@"symbolic _____ s5Int64V" = linkonce_odr hidden constant <{ i8, i32, i8 }> <{ i8 2, i32 trunc (i64 sub (i64 ptrtoint (ptr @"got.$ss5Int64VMn" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i8, i32, i8 }>, ptr @"symbolic _____ s5Int64V", i32 0, i32 1) to i64)) to i32), i8 0 }>, section "swift5_typeref", no_sanitize_address, align 2
@0 = private constant [2 x i8] c"n\00", section "swift5_reflstr", no_sanitize_address
@"$s11swift_types7CounterCMF" = internal constant { i32, i32, i16, i16, i32, i32, i32, i32 } { i32 trunc (i64 sub (i64 ptrtoint (ptr @"symbolic _____ 11swift_types7CounterC" to i64), i64 ptrtoint (ptr @"$s11swift_types7CounterCMF" to i64)) to i32), i32 0, i16 1, i16 12, i32 1, i32 2, i32 trunc (i64 sub (i64 ptrtoint (ptr @"symbolic _____ s5Int64V" to i64), i64 ptrtoint (ptr getelementptr inbounds ({ i32, i32, i16, i16, i32, i32, i32, i32 }, ptr @"$s11swift_types7CounterCMF", i32 0, i32 6) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @0 to i64), i64 ptrtoint (ptr getelementptr inbounds ({ i32, i32, i16, i16, i32, i32, i32, i32 }, ptr @"$s11swift_types7CounterCMF", i32 0, i32 7) to i64)) to i32) }, section "swift5_fieldmd", no_sanitize_address, align 4
@"$s11swift_types4PairVWV" = internal constant %swift.vwtable { ptr @__swift_memcpy16_8, ptr @__swift_noop_void_return, ptr @__swift_memcpy16_8, ptr @__swift_memcpy16_8, ptr @__swift_memcpy16_8, ptr @__swift_memcpy16_8, ptr @"$s11swift_types4PairVwet", ptr @"$s11swift_types4PairVwst", i64 16, i64 16, i32 7, i32 0 }, align 8
@.str.4.Pair = private constant [5 x i8] c"Pair\00"
@"$s11swift_types4PairVMn" = hidden constant <{ i32, i32, i32, i32, i32, i32, i32 }> <{ i32 81, i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_typesMXM" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32 }>, ptr @"$s11swift_types4PairVMn", i32 0, i32 1) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @.str.4.Pair to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32 }>, ptr @"$s11swift_types4PairVMn", i32 0, i32 2) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types4PairVMa" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32 }>, ptr @"$s11swift_types4PairVMn", i32 0, i32 3) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types4PairVMF" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32 }>, ptr @"$s11swift_types4PairVMn", i32 0, i32 4) to i64)) to i32), i32 2, i32 2 }>, section ".rodata", no_sanitize_address, align 4
@"$s11swift_types4PairVMf" = internal constant <{ ptr, ptr, i64, ptr, i32, i32 }> <{ ptr null, ptr @"$s11swift_types4PairVWV", i64 512, ptr @"$s11swift_types4PairVMn", i32 0, i32 8 }>, align 8
@"symbolic _____ 11swift_types4PairV" = linkonce_odr hidden constant <{ i8, i32, i8 }> <{ i8 1, i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types4PairVMn" to i64), i64 ptrtoint (ptr getelementptr inbounds (<{ i8, i32, i8 }>, ptr @"symbolic _____ 11swift_types4PairV", i32 0, i32 1) to i64)) to i32), i8 0 }>, section "swift5_typeref", no_sanitize_address, align 2
@1 = private constant [2 x i8] c"a\00", section "swift5_reflstr", no_sanitize_address
@2 = private constant [2 x i8] c"b\00", section "swift5_reflstr", no_sanitize_address
@"$s11swift_types4PairVMF" = internal constant { i32, i32, i16, i16, i32, i32, i32, i32, i32, i32, i32 } { i32 trunc (i64 sub (i64 ptrtoint (ptr @"symbolic _____ 11swift_types4PairV" to i64), i64 ptrtoint (ptr @"$s11swift_types4PairVMF" to i64)) to i32), i32 0, i16 0, i16 12, i32 2, i32 2, i32 trunc (i64 sub (i64 ptrtoint (ptr @"symbolic _____ s5Int64V" to i64), i64 ptrtoint (ptr getelementptr inbounds ({ i32, i32, i16, i16, i32, i32, i32, i32, i32, i32, i32 }, ptr @"$s11swift_types4PairVMF", i32 0, i32 6) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @1 to i64), i64 ptrtoint (ptr getelementptr inbounds ({ i32, i32, i16, i16, i32, i32, i32, i32, i32, i32, i32 }, ptr @"$s11swift_types4PairVMF", i32 0, i32 7) to i64)) to i32), i32 2, i32 trunc (i64 sub (i64 ptrtoint (ptr @"symbolic _____ s5Int64V" to i64), i64 ptrtoint (ptr getelementptr inbounds ({ i32, i32, i16, i16, i32, i32, i32, i32, i32, i32, i32 }, ptr @"$s11swift_types4PairVMF", i32 0, i32 9) to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @2 to i64), i64 ptrtoint (ptr getelementptr inbounds ({ i32, i32, i16, i16, i32, i32, i32, i32, i32, i32, i32 }, ptr @"$s11swift_types4PairVMF", i32 0, i32 10) to i64)) to i32) }, section "swift5_fieldmd", no_sanitize_address, align 4
@"$s11swift_types7CounterCHn" = private constant %swift.type_metadata_record { i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types7CounterCMn" to i64), i64 ptrtoint (ptr @"$s11swift_types7CounterCHn" to i64)) to i32) }, section "swift5_type_metadata", no_sanitize_address, align 4
@"$s11swift_types4PairVHn" = private constant %swift.type_metadata_record { i32 trunc (i64 sub (i64 ptrtoint (ptr @"$s11swift_types4PairVMn" to i64), i64 ptrtoint (ptr @"$s11swift_types4PairVHn" to i64)) to i32) }, section "swift5_type_metadata", no_sanitize_address, align 4
@__swift_reflection_version = linkonce_odr hidden constant i16 3
@_swift1_autolink_entries = private constant [102 x i8] c"-lswiftSwiftOnoneSupport\00-lswiftCore\00-lswift_Concurrency\00-lswift_StringProcessing\00-lswift_RegexParser\00", section ".swift1_autolink_entries", no_sanitize_address, align 8
@llvm.used = appending global [16 x ptr] [ptr @main, ptr @"$s11swift_types7CounterC1ns5Int64Vvg", ptr @"$s11swift_types7CounterC1ns5Int64Vvs", ptr @read_class, ptr @"$s11swift_types4PairV1as5Int64Vvg", ptr @"$s11swift_types4PairV1as5Int64Vvs", ptr @"$s11swift_types4PairV1bs5Int64Vvg", ptr @"$s11swift_types4PairV1bs5Int64Vvs", ptr @sum_inout, ptr @"\01l_entry_point", ptr @"$s11swift_types7CounterCMF", ptr @"$s11swift_types4PairVMF", ptr @"$s11swift_types7CounterCHn", ptr @"$s11swift_types4PairVHn", ptr @__swift_reflection_version, ptr @_swift1_autolink_entries], section "llvm.metadata"
@llvm.compiler.used = appending global [5 x ptr] [ptr @"$s11swift_types7CounterCACycfCTq", ptr @"$s11swift_types7CounterCMf", ptr @"$s11swift_types7CounterCN", ptr @"$s11swift_types4PairVMf", ptr @"$s11swift_types4PairVN"], section "llvm.metadata"

@"$s11swift_types7CounterCACycfCTq" = hidden alias %swift.method_descriptor, getelementptr inbounds (<{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, %swift.method_descriptor }>, ptr @"$s11swift_types7CounterCMn", i32 0, i32 13)
@"$s11swift_types7CounterCN" = hidden alias %swift.type, getelementptr inbounds (<{ ptr, ptr, ptr, i64, ptr, i32, i32, i32, i16, i16, i32, i32, ptr, ptr, i64, ptr }>, ptr @"$s11swift_types7CounterCMf", i32 0, i32 3)
@"$s11swift_types4PairVN" = hidden alias %swift.type, getelementptr inbounds (<{ ptr, ptr, i64, ptr, i32, i32 }>, ptr @"$s11swift_types4PairVMf", i32 0, i32 2)

define protected i32 @main(i32 %0, ptr %1) #0 !dbg !28 {
entry:
  ret i32 0, !dbg !33
}

define hidden swiftcc i64 @"$s11swift_types7CounterC1ns5Int64Vvpfi"() #0 !dbg !36 {
entry:
  ret i64 0, !dbg !40
}

define hidden swiftcc i64 @"$s11swift_types7CounterC1ns5Int64Vvg"(ptr swiftself %0) #0 !dbg !41 {
entry:
  %access-scratch = alloca [24 x i8], align 8
  %1 = getelementptr inbounds nuw %T11swift_types7CounterC, ptr %0, i32 0, i32 1, !dbg !46
  call void @llvm.lifetime.start.p0(i64 -1, ptr %access-scratch), !dbg !46
  call void @swift_beginAccess(ptr %1, ptr %access-scratch, i64 32, ptr null) #2, !dbg !46
  %._value = getelementptr inbounds nuw %Ts5Int64V, ptr %1, i32 0, i32 0, !dbg !46
  %2 = load i64, ptr %._value, align 8, !dbg !46
  call void @swift_endAccess(ptr %access-scratch) #2, !dbg !46
  call void @llvm.lifetime.end.p0(i64 -1, ptr %access-scratch), !dbg !46
  ret i64 %2, !dbg !46
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(i64 immarg, ptr captures(none)) #1

; Function Attrs: nounwind
declare void @swift_beginAccess(ptr, ptr, i64, ptr) #2

; Function Attrs: nounwind
declare void @swift_endAccess(ptr) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(i64 immarg, ptr captures(none)) #1

define hidden swiftcc void @"$s11swift_types7CounterC1ns5Int64Vvs"(i64 %0, ptr swiftself %1) #0 !dbg !47 {
entry:
  %access-scratch = alloca [24 x i8], align 8
  %2 = getelementptr inbounds nuw %T11swift_types7CounterC, ptr %1, i32 0, i32 1, !dbg !52
  call void @llvm.lifetime.start.p0(i64 -1, ptr %access-scratch), !dbg !52
  call void @swift_beginAccess(ptr %2, ptr %access-scratch, i64 33, ptr null) #2, !dbg !52
  %._value = getelementptr inbounds nuw %Ts5Int64V, ptr %2, i32 0, i32 0, !dbg !52
  store i64 %0, ptr %._value, align 8, !dbg !52
  call void @swift_endAccess(ptr %access-scratch) #2, !dbg !52
  call void @llvm.lifetime.end.p0(i64 -1, ptr %access-scratch), !dbg !52
  ret void, !dbg !52
}

; Function Attrs: noinline
define hidden swiftcc { ptr, ptr } @"$s11swift_types7CounterC1ns5Int64VvM"(ptr noalias dereferenceable(32) %0, ptr swiftself %1) #3 !dbg !53 {
entry:
  %access-scratch = getelementptr inbounds %"$s11swift_types7CounterC1ns5Int64VvM.Frame", ptr %0, i32 0, i32 0, !dbg !57
  %2 = getelementptr inbounds nuw %T11swift_types7CounterC, ptr %1, i32 0, i32 1, !dbg !57
  call void @llvm.lifetime.start.p0(i64 -1, ptr %access-scratch), !dbg !57
  call void @swift_beginAccess(ptr %2, ptr %access-scratch, i64 33, ptr null) #2, !dbg !57
  %3 = insertvalue { ptr, ptr } poison, ptr @"$s11swift_types7CounterC1ns5Int64VvM.resume.0", 0
  %4 = insertvalue { ptr, ptr } %3, ptr %2, 1
  ret { ptr, ptr } %4
}

define internal swiftcc void @"$s11swift_types7CounterC1ns5Int64VvM.resume.0"(ptr noalias noundef nonnull align 8 dereferenceable(32) %0, i1 %1) #0 !dbg !58 {
entryresume.0:
  %access-scratch = getelementptr inbounds %"$s11swift_types7CounterC1ns5Int64VvM.Frame", ptr %0, i32 0, i32 0, !dbg !60
  call void @swift_endAccess(ptr %access-scratch) #2, !dbg !60
  call void @llvm.lifetime.end.p0(i64 -1, ptr %access-scratch), !dbg !60
  ret void, !dbg !60
}

define hidden swiftcc ptr @"$s11swift_types7CounterCfd"(ptr swiftself %0) #0 !dbg !61 {
entry:
  %self.debug = alloca ptr, align 8
    #dbg_declare(ptr %self.debug, !68, !DIExpression(), !70)
  call void @llvm.memset.p0.i64(ptr align 8 %self.debug, i8 0, i64 8, i1 false)
  store ptr %0, ptr %self.debug, align 8, !dbg !71
  ret ptr %0, !dbg !71
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #4

define hidden swiftcc void @"$s11swift_types7CounterCfD"(ptr swiftself %0) #0 !dbg !72 {
entry:
  %self.debug = alloca ptr, align 8
    #dbg_declare(ptr %self.debug, !75, !DIExpression(), !76)
  call void @llvm.memset.p0.i64(ptr align 8 %self.debug, i8 0, i64 8, i1 false)
  store ptr %0, ptr %self.debug, align 8, !dbg !77
  %1 = call swiftcc ptr @"$s11swift_types7CounterCfd"(ptr swiftself %0), !dbg !77
  call void @swift_deallocClassInstance(ptr %1, i64 24, i64 7) #2, !dbg !77
  ret void, !dbg !77
}

; Function Attrs: nounwind
declare void @swift_deallocClassInstance(ptr, i64, i64) #2

define hidden swiftcc ptr @"$s11swift_types7CounterCACycfC"(ptr swiftself %0) #0 !dbg !78 {
entry:
  %1 = call noalias ptr @swift_allocObject(ptr %0, i64 24, i64 7) #2, !dbg !83
  %2 = call swiftcc ptr @"$s11swift_types7CounterCACycfc"(ptr swiftself %1), !dbg !83
  ret ptr %2, !dbg !83
}

; Function Attrs: nounwind
declare ptr @swift_allocObject(ptr, i64, i64) #2

define hidden swiftcc ptr @"$s11swift_types7CounterCACycfc"(ptr swiftself %0) #0 !dbg !84 {
entry:
  %self.debug = alloca ptr, align 8
    #dbg_declare(ptr %self.debug, !89, !DIExpression(), !90)
  call void @llvm.memset.p0.i64(ptr align 8 %self.debug, i8 0, i64 8, i1 false)
  store ptr %0, ptr %self.debug, align 8, !dbg !91
  %1 = getelementptr inbounds nuw %T11swift_types7CounterC, ptr %0, i32 0, i32 1, !dbg !92
  %._value = getelementptr inbounds nuw %Ts5Int64V, ptr %1, i32 0, i32 0, !dbg !95
  store i64 0, ptr %._value, align 8, !dbg !95
  ret ptr %0, !dbg !97
}

define hidden swiftcc i64 @read_class(ptr %0) #0 !dbg !98 {
entry:
  %c.debug = alloca ptr, align 8
    #dbg_declare(ptr %c.debug, !100, !DIExpression(), !101)
  call void @llvm.memset.p0.i64(ptr align 8 %c.debug, i8 0, i64 8, i1 false)
  %access-scratch = alloca [24 x i8], align 8
  store ptr %0, ptr %c.debug, align 8, !dbg !102
  %1 = getelementptr inbounds nuw %T11swift_types7CounterC, ptr %0, i32 0, i32 1, !dbg !103
  call void @llvm.lifetime.start.p0(i64 -1, ptr %access-scratch), !dbg !103
  call void @swift_beginAccess(ptr %1, ptr %access-scratch, i64 32, ptr null) #2, !dbg !103
  %._value = getelementptr inbounds nuw %Ts5Int64V, ptr %1, i32 0, i32 0, !dbg !103
  %2 = load i64, ptr %._value, align 8, !dbg !103
  call void @swift_endAccess(ptr %access-scratch) #2, !dbg !102
  call void @llvm.lifetime.end.p0(i64 -1, ptr %access-scratch), !dbg !102
  ret i64 %2, !dbg !104
}

define hidden swiftcc i64 @"$s11swift_types4PairV1as5Int64Vvg"(i64 %0, i64 %1) #0 !dbg !105 {
entry:
  ret i64 %0, !dbg !110
}

define hidden swiftcc void @"$s11swift_types4PairV1as5Int64Vvs"(i64 %0, ptr swiftself captures(none) dereferenceable(16) %1) #0 !dbg !111 {
entry:
  %.a = getelementptr inbounds nuw %T11swift_types4PairV, ptr %1, i32 0, i32 0, !dbg !115
  %.a._value = getelementptr inbounds nuw %Ts5Int64V, ptr %.a, i32 0, i32 0, !dbg !115
  store i64 %0, ptr %.a._value, align 8, !dbg !115
  ret void, !dbg !115
}

; Function Attrs: noinline
define hidden swiftcc { ptr, ptr } @"$s11swift_types4PairV1as5Int64VvM"(ptr noalias dereferenceable(32) %0, ptr swiftself captures(none) dereferenceable(16) %1) #3 !dbg !116 {
entry:
  %.a = getelementptr inbounds nuw %T11swift_types4PairV, ptr %1, i32 0, i32 0, !dbg !120
  %2 = insertvalue { ptr, ptr } poison, ptr @"$s11swift_types4PairV1as5Int64VvM.resume.0", 0
  %3 = insertvalue { ptr, ptr } %2, ptr %.a, 1
  ret { ptr, ptr } %3
}

define internal swiftcc void @"$s11swift_types4PairV1as5Int64VvM.resume.0"(ptr noalias noundef nonnull align 8 dereferenceable(32) %0, i1 %1) #0 !dbg !121 {
entryresume.0:
  ret void, !dbg !123
}

define hidden swiftcc i64 @"$s11swift_types4PairV1bs5Int64Vvg"(i64 %0, i64 %1) #0 !dbg !124 {
entry:
  ret i64 %1, !dbg !126
}

define hidden swiftcc void @"$s11swift_types4PairV1bs5Int64Vvs"(i64 %0, ptr swiftself captures(none) dereferenceable(16) %1) #0 !dbg !127 {
entry:
  %.b = getelementptr inbounds nuw %T11swift_types4PairV, ptr %1, i32 0, i32 1, !dbg !129
  %.b._value = getelementptr inbounds nuw %Ts5Int64V, ptr %.b, i32 0, i32 0, !dbg !129
  store i64 %0, ptr %.b._value, align 8, !dbg !129
  ret void, !dbg !129
}

; Function Attrs: noinline
define hidden swiftcc { ptr, ptr } @"$s11swift_types4PairV1bs5Int64VvM"(ptr noalias dereferenceable(32) %0, ptr swiftself captures(none) dereferenceable(16) %1) #3 !dbg !130 {
entry:
  %.b = getelementptr inbounds nuw %T11swift_types4PairV, ptr %1, i32 0, i32 1, !dbg !132
  %2 = insertvalue { ptr, ptr } poison, ptr @"$s11swift_types4PairV1bs5Int64VvM.resume.0", 0
  %3 = insertvalue { ptr, ptr } %2, ptr %.b, 1
  ret { ptr, ptr } %3
}

define internal swiftcc void @"$s11swift_types4PairV1bs5Int64VvM.resume.0"(ptr noalias noundef nonnull align 8 dereferenceable(32) %0, i1 %1) #0 !dbg !133 {
entryresume.0:
  ret void, !dbg !135
}

define hidden swiftcc { i64, i64 } @"$s11swift_types4PairV1a1bACs5Int64V_AGtcfC"(i64 %0, i64 %1) #0 !dbg !136 {
entry:
  %2 = insertvalue { i64, i64 } undef, i64 %0, 0, !dbg !141
  %3 = insertvalue { i64, i64 } %2, i64 %1, 1, !dbg !141
  ret { i64, i64 } %3, !dbg !141
}

define hidden swiftcc i64 @sum_inout(ptr captures(none) dereferenceable(16) %0) #0 !dbg !142 {
entry:
  %p.debug = alloca ptr, align 8
    #dbg_declare(ptr %p.debug, !144, !DIExpression(DW_OP_deref), !145)
  call void @llvm.memset.p0.i64(ptr align 8 %p.debug, i8 0, i64 8, i1 false)
  store ptr %0, ptr %p.debug, align 8, !dbg !146
  %.a = getelementptr inbounds nuw %T11swift_types4PairV, ptr %0, i32 0, i32 0, !dbg !147
  %.a._value = getelementptr inbounds nuw %Ts5Int64V, ptr %.a, i32 0, i32 0, !dbg !147
  %1 = load i64, ptr %.a._value, align 8, !dbg !147
  %.b = getelementptr inbounds nuw %T11swift_types4PairV, ptr %0, i32 0, i32 1, !dbg !148
  %.b._value = getelementptr inbounds nuw %Ts5Int64V, ptr %.b, i32 0, i32 0, !dbg !148
  %2 = load i64, ptr %.b._value, align 8, !dbg !148
  %3 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %1, i64 %2), !dbg !149
  %4 = extractvalue { i64, i1 } %3, 0, !dbg !149
  %5 = extractvalue { i64, i1 } %3, 1, !dbg !149
  %6 = call i1 @llvm.expect.i1(i1 %5, i1 false), !dbg !149
  br i1 %6, label %8, label %7, !dbg !149

7:                                                ; preds = %entry
  ret i64 %4, !dbg !150

8:                                                ; preds = %entry
  call void @llvm.trap(), !dbg !151
  unreachable, !dbg !151
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64) #5

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(none)
declare i1 @llvm.expect.i1(i1, i1) #6

; Function Attrs: cold noreturn nounwind memory(inaccessiblemem: write)
declare void @llvm.trap() #7

; Function Attrs: noinline nounwind memory(none)
define hidden swiftcc %swift.metadata_response @"$s11swift_types7CounterCMa"(i64 %0) #8 !dbg !154 {
entry:
  ret %swift.metadata_response { ptr getelementptr inbounds (<{ ptr, ptr, ptr, i64, ptr, i32, i32, i32, i16, i16, i32, i32, ptr, ptr, i64, ptr }>, ptr @"$s11swift_types7CounterCMf", i32 0, i32 3), i64 0 }, !dbg !155
}

; Function Attrs: nounwind
define linkonce_odr hidden ptr @__swift_memcpy16_8(ptr %0, ptr %1, ptr %2) #9 !dbg !156 {
entry:
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %0, ptr align 8 %1, i64 16, i1 false), !dbg !157
  ret ptr %0, !dbg !157
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #10

; Function Attrs: nounwind
define linkonce_odr hidden void @__swift_noop_void_return(ptr %0, ptr %1) #9 !dbg !158 {
entry:
  ret void, !dbg !159
}

; Function Attrs: nounwind memory(read)
define internal i32 @"$s11swift_types4PairVwet"(ptr noalias %value, i32 %numEmptyCases, ptr %Pair) #11 !dbg !160 {
entry:
  %0 = icmp eq i32 0, %numEmptyCases, !dbg !161
  br i1 %0, label %31, label %1, !dbg !161

1:                                                ; preds = %entry
  %2 = icmp ugt i32 %numEmptyCases, 0, !dbg !161
  br i1 %2, label %3, label %30, !dbg !161

3:                                                ; preds = %1
  %4 = sub i32 %numEmptyCases, 0, !dbg !161
  %5 = getelementptr inbounds i8, ptr %value, i32 16, !dbg !161
  br i1 false, label %6, label %7, !dbg !161

6:                                                ; preds = %3
  br label %19, !dbg !161

7:                                                ; preds = %3
  br i1 true, label %8, label %11, !dbg !161

8:                                                ; preds = %7
  %9 = load i8, ptr %5, align 1, !dbg !161
  %10 = zext i8 %9 to i32, !dbg !161
  br label %19, !dbg !161

11:                                               ; preds = %7
  br i1 false, label %12, label %15, !dbg !161

12:                                               ; preds = %11
  %13 = load i16, ptr %5, align 1, !dbg !161
  %14 = zext i16 %13 to i32, !dbg !161
  br label %19, !dbg !161

15:                                               ; preds = %11
  br i1 false, label %16, label %18, !dbg !161

16:                                               ; preds = %15
  %17 = load i32, ptr %5, align 1, !dbg !161
  br label %19, !dbg !161

18:                                               ; preds = %15
  unreachable, !dbg !161

19:                                               ; preds = %16, %12, %8, %6
  %20 = phi i32 [ 0, %6 ], [ %10, %8 ], [ %14, %12 ], [ %17, %16 ], !dbg !161
  %21 = icmp eq i32 %20, 0, !dbg !161
  br i1 %21, label %30, label %22, !dbg !161

22:                                               ; preds = %19
  %23 = sub i32 %20, 1, !dbg !161
  %24 = shl i32 %23, 128, !dbg !161
  %25 = select i1 true, i32 0, i32 %24, !dbg !161
  %26 = load i128, ptr %value, align 1, !dbg !161
  %27 = trunc i128 %26 to i32, !dbg !161
  %28 = or i32 %27, %25, !dbg !161
  %29 = add i32 0, %28, !dbg !161
  br label %32, !dbg !161

30:                                               ; preds = %19, %1
  br label %32, !dbg !161

31:                                               ; preds = %entry
  br label %32, !dbg !161

32:                                               ; preds = %31, %30, %22
  %33 = phi i32 [ -1, %30 ], [ %29, %22 ], [ -1, %31 ], !dbg !161
  %34 = add i32 %33, 1, !dbg !161
  ret i32 %34, !dbg !161
}

; Function Attrs: nounwind
define internal void @"$s11swift_types4PairVwst"(ptr noalias %value, i32 %whichCase, i32 %numEmptyCases, ptr %Pair) #9 !dbg !162 {
entry:
  %0 = getelementptr inbounds i8, ptr %value, i32 16, !dbg !163
  %1 = icmp ugt i32 %numEmptyCases, 0, !dbg !163
  br i1 %1, label %2, label %4, !dbg !163

2:                                                ; preds = %entry
  %3 = sub i32 %numEmptyCases, 0, !dbg !163
  br label %4, !dbg !163

4:                                                ; preds = %2, %entry
  %5 = phi i32 [ 0, %entry ], [ 1, %2 ], !dbg !163
  %6 = icmp ule i32 %whichCase, 0, !dbg !163
  br i1 %6, label %7, label %23, !dbg !163

7:                                                ; preds = %4
  %8 = icmp eq i32 %5, 0, !dbg !163
  br i1 %8, label %9, label %10, !dbg !163

9:                                                ; preds = %7
  br label %20, !dbg !163

10:                                               ; preds = %7
  %11 = icmp eq i32 %5, 1, !dbg !163
  br i1 %11, label %12, label %13, !dbg !163

12:                                               ; preds = %10
  store i8 0, ptr %0, align 8, !dbg !163
  br label %20, !dbg !163

13:                                               ; preds = %10
  %14 = icmp eq i32 %5, 2, !dbg !163
  br i1 %14, label %15, label %16, !dbg !163

15:                                               ; preds = %13
  store i16 0, ptr %0, align 8, !dbg !163
  br label %20, !dbg !163

16:                                               ; preds = %13
  %17 = icmp eq i32 %5, 4, !dbg !163
  br i1 %17, label %18, label %19, !dbg !163

18:                                               ; preds = %16
  store i32 0, ptr %0, align 8, !dbg !163
  br label %20, !dbg !163

19:                                               ; preds = %16
  unreachable, !dbg !163

20:                                               ; preds = %18, %15, %12, %9
  %21 = icmp eq i32 %whichCase, 0, !dbg !163
  br i1 %21, label %49, label %22, !dbg !163

22:                                               ; preds = %20
  br label %49, !dbg !163

23:                                               ; preds = %4
  %24 = sub i32 %whichCase, 1, !dbg !163
  %25 = sub i32 %24, 0, !dbg !163
  br i1 true, label %30, label %26, !dbg !163

26:                                               ; preds = %23
  %27 = lshr i32 %25, 128, !dbg !163
  %28 = add i32 1, %27, !dbg !163
  %29 = and i32 poison, %25, !dbg !163
  br label %30, !dbg !163

30:                                               ; preds = %26, %23
  %31 = phi i32 [ 1, %23 ], [ %28, %26 ], !dbg !163
  %32 = phi i32 [ %25, %23 ], [ %29, %26 ], !dbg !163
  %33 = zext i32 %32 to i128, !dbg !163
  store i128 %33, ptr %value, align 8, !dbg !163
  %34 = icmp eq i32 %5, 0, !dbg !163
  br i1 %34, label %35, label %36, !dbg !163

35:                                               ; preds = %30
  br label %48, !dbg !163

36:                                               ; preds = %30
  %37 = icmp eq i32 %5, 1, !dbg !163
  br i1 %37, label %38, label %40, !dbg !163

38:                                               ; preds = %36
  %39 = trunc i32 %31 to i8, !dbg !163
  store i8 %39, ptr %0, align 8, !dbg !163
  br label %48, !dbg !163

40:                                               ; preds = %36
  %41 = icmp eq i32 %5, 2, !dbg !163
  br i1 %41, label %42, label %44, !dbg !163

42:                                               ; preds = %40
  %43 = trunc i32 %31 to i16, !dbg !163
  store i16 %43, ptr %0, align 8, !dbg !163
  br label %48, !dbg !163

44:                                               ; preds = %40
  %45 = icmp eq i32 %5, 4, !dbg !163
  br i1 %45, label %46, label %47, !dbg !163

46:                                               ; preds = %44
  store i32 %31, ptr %0, align 8, !dbg !163
  br label %48, !dbg !163

47:                                               ; preds = %44
  unreachable, !dbg !163

48:                                               ; preds = %46, %42, %38, %35
  br label %49, !dbg !163

49:                                               ; preds = %48, %22, %20
  ret void, !dbg !163
}

; Function Attrs: noinline nounwind memory(none)
define hidden swiftcc %swift.metadata_response @"$s11swift_types4PairVMa"(i64 %0) #8 !dbg !164 {
entry:
  ret %swift.metadata_response { ptr getelementptr inbounds (<{ ptr, ptr, i64, ptr, i32, i32 }>, ptr @"$s11swift_types4PairVMf", i32 0, i32 2), i64 0 }, !dbg !165
}

attributes #0 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx16,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #2 = { nounwind }
attributes #3 = { noinline "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx16,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #5 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #6 = { nocallback nofree nosync nounwind willreturn memory(none) }
attributes #7 = { cold noreturn nounwind memory(inaccessiblemem: write) }
attributes #8 = { noinline nounwind memory(none) "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx16,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #9 = { nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx16,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #10 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #11 = { nounwind memory(read) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx16,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0, !15, !17}
!swift.module.flags = !{!19}
!llvm.module.flags = !{!20, !21, !22, !23, !24, !25, !26, !27}
!llvm.linker.options = !{}

!0 = distinct !DICompileUnit(language: DW_LANG_Swift, file: !1, producer: "Swift version 6.3.3 (swift-6.3.3-RELEASE)", isOptimized: false, runtimeVersion: 6, emissionKind: FullDebug, imports: !2)
!1 = !DIFile(filename: "tests/dwarf-corpus/swift_types.swift", directory: "/home/simon/Schreibtisch/CSolver")
!2 = !{!3, !5, !7, !9, !11, !13}
!3 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !1, entity: !4, file: !1)
!4 = !DIModule(scope: null, name: "swift_types", includePath: "tests/dwarf-corpus")
!5 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !1, entity: !6, file: !1)
!6 = !DIModule(scope: null, name: "Swift", includePath: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/swift-6.3.3-RELEASE-ubuntu24.04/usr/lib/swift/linux/Swift.swiftmodule/x86_64-unknown-linux-gnu.swiftmodule")
!7 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !1, entity: !8, file: !1)
!8 = !DIModule(scope: null, name: "_StringProcessing", includePath: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/swift-6.3.3-RELEASE-ubuntu24.04/usr/lib/swift/linux/_StringProcessing.swiftmodule/x86_64-unknown-linux-gnu.swiftmodule")
!9 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !1, entity: !10, file: !1)
!10 = !DIModule(scope: null, name: "_SwiftConcurrencyShims", includePath: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/swift-6.3.3-RELEASE-ubuntu24.04/usr/lib/swift/shims")
!11 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !1, entity: !12, file: !1)
!12 = !DIModule(scope: null, name: "_Concurrency", includePath: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/swift-6.3.3-RELEASE-ubuntu24.04/usr/lib/swift/linux/_Concurrency.swiftmodule/x86_64-unknown-linux-gnu.swiftmodule")
!13 = !DIImportedEntity(tag: DW_TAG_imported_module, scope: !1, entity: !14, file: !1)
!14 = !DIModule(scope: null, name: "SwiftOnoneSupport", includePath: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/swift-6.3.3-RELEASE-ubuntu24.04/usr/lib/swift/linux/SwiftOnoneSupport.swiftmodule/x86_64-unknown-linux-gnu.swiftmodule")
!15 = distinct !DICompileUnit(language: DW_LANG_C11, file: !16, producer: "clang version 21.0.0 (https://github.com/swiftlang/llvm-project.git 82cdc19fa54d566969527b56f587ea8ea30bef51)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!16 = !DIFile(filename: "<swift-imported-modules>", directory: "/home/simon/Schreibtisch/CSolver")
!17 = distinct !DICompileUnit(language: DW_LANG_C99, file: !18, producer: "Swift version 6.3.3 (swift-6.3.3-RELEASE)", isOptimized: true, runtimeVersion: 0, splitDebugFilename: "/home/simon/.cache/clang/ModuleCache/2SZA1T8FCMAYL/_SwiftConcurrencyShims-1Z3WDYNK7H70F.pcm", emissionKind: FullDebug, dwoId: 4768473122253145535)
!18 = !DIFile(filename: "_SwiftConcurrencyShims", directory: "/tmp/claude-1000/-home-simon-Schreibtisch-CSolver/3c91bbab-e34c-4c88-a1d1-11049a65645a/scratchpad/tc/swift-6.3.3-RELEASE-ubuntu24.04/usr/lib/swift/shims")
!19 = !{!"standard-library", i1 false}
!20 = !{i32 7, !"Dwarf Version", i32 4}
!21 = !{i32 2, !"Debug Info Version", i32 3}
!22 = !{i32 1, !"wchar_size", i32 4}
!23 = !{i32 8, !"PIC Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{i32 4, !"Objective-C Garbage Collection", i32 100861696}
!27 = !{i32 1, !"Swift Version", i32 7}
!28 = distinct !DISubprogram(name: "main", linkageName: "main", scope: !4, file: !1, line: 1, type: !29, spFlags: DISPFlagDefinition, unit: !0)
!29 = !DISubroutineType(types: !30)
!30 = !{!31, !31, !32}
!31 = !DICompositeType(tag: DW_TAG_structure_type, name: "Int32", scope: !6, flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$ss5Int32VD")
!32 = !DICompositeType(tag: DW_TAG_structure_type, name: "UnsafeMutablePointer", scope: !6, flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$sSpySpys4Int8VGSgGD")
!33 = !DILocation(line: 0, scope: !34)
!34 = !DILexicalBlockFile(scope: !28, file: !35, discriminator: 0)
!35 = !DIFile(filename: "<compiler-generated>", directory: "/")
!36 = distinct !DISubprogram(linkageName: "$s11swift_types7CounterC1ns5Int64Vvpfi", scope: !4, file: !35, type: !37, flags: DIFlagArtificial, spFlags: DISPFlagDefinition, unit: !0)
!37 = !DISubroutineType(types: !38)
!38 = !{!39}
!39 = !DICompositeType(tag: DW_TAG_structure_type, name: "Int64", scope: !6, flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$ss5Int64VD")
!40 = !DILocation(line: 0, scope: !36)
!41 = distinct !DISubprogram(name: "n.get", linkageName: "$s11swift_types7CounterC1ns5Int64Vvg", scope: !42, file: !35, type: !43, spFlags: DISPFlagDefinition, unit: !0, declaration: !45)
!42 = !DICompositeType(tag: DW_TAG_structure_type, name: "Counter", scope: !4, file: !1, size: 64, runtimeLang: DW_LANG_Swift, identifier: "$s11swift_types7CounterCD")
!43 = !DISubroutineType(types: !44)
!44 = !{!39, !42}
!45 = !DISubprogram(name: "n.get", linkageName: "$s11swift_types7CounterC1ns5Int64Vvg", scope: !42, file: !35, type: !43, spFlags: 0)
!46 = !DILocation(line: 0, scope: !41)
!47 = distinct !DISubprogram(name: "n.set", linkageName: "$s11swift_types7CounterC1ns5Int64Vvs", scope: !42, file: !35, type: !48, spFlags: DISPFlagDefinition, unit: !0, declaration: !51)
!48 = !DISubroutineType(types: !49)
!49 = !{!50, !39, !42}
!50 = !DICompositeType(tag: DW_TAG_structure_type, name: "$sytD", flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$sytD")
!51 = !DISubprogram(name: "n.set", linkageName: "$s11swift_types7CounterC1ns5Int64Vvs", scope: !42, file: !35, type: !48, spFlags: 0)
!52 = !DILocation(line: 0, scope: !47)
!53 = distinct !DISubprogram(name: "n.modify", linkageName: "$s11swift_types7CounterC1ns5Int64VvM", scope: !42, file: !35, type: !54, spFlags: DISPFlagDefinition, unit: !0, declaration: !56)
!54 = !DISubroutineType(types: !55)
!55 = !{!50, !42}
!56 = !DISubprogram(name: "n.modify", linkageName: "$s11swift_types7CounterC1ns5Int64VvM", scope: !42, file: !35, type: !54, spFlags: 0)
!57 = !DILocation(line: 0, scope: !53)
!58 = distinct !DISubprogram(name: "n.modify", linkageName: "$s11swift_types7CounterC1ns5Int64VvM.resume.0", scope: !42, file: !35, type: !54, spFlags: DISPFlagDefinition, unit: !0, declaration: !59)
!59 = !DISubprogram(name: "n.modify", linkageName: "$s11swift_types7CounterC1ns5Int64VvM.resume.0", scope: !42, file: !35, type: !54, spFlags: 0)
!60 = !DILocation(line: 0, scope: !58)
!61 = distinct !DISubprogram(name: "deinit", linkageName: "$s11swift_types7CounterCfd", scope: !42, file: !1, line: 3, type: !62, scopeLine: 3, spFlags: DISPFlagDefinition, unit: !0, declaration: !66, retainedNodes: !67)
!62 = !DISubroutineType(types: !63)
!63 = !{!64, !42}
!64 = !DICompositeType(tag: DW_TAG_structure_type, name: "$sBoD", scope: !65, flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$sBoD")
!65 = !DIModule(scope: null, name: "Builtin")
!66 = !DISubprogram(name: "deinit", linkageName: "$s11swift_types7CounterCfd", scope: !42, file: !1, line: 3, type: !62, scopeLine: 3, spFlags: 0)
!67 = !{!68}
!68 = !DILocalVariable(name: "self", arg: 1, scope: !61, file: !1, line: 3, type: !69, flags: DIFlagArtificial)
!69 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !42)
!70 = !DILocation(line: 3, column: 13, scope: !61)
!71 = !DILocation(line: 0, scope: !61)
!72 = distinct !DISubprogram(name: "deinit", linkageName: "$s11swift_types7CounterCfD", scope: !42, file: !1, line: 3, type: !54, scopeLine: 3, spFlags: DISPFlagDefinition, unit: !0, declaration: !73, retainedNodes: !74)
!73 = !DISubprogram(name: "deinit", linkageName: "$s11swift_types7CounterCfD", scope: !42, file: !1, line: 3, type: !54, scopeLine: 3, spFlags: 0)
!74 = !{!75}
!75 = !DILocalVariable(name: "self", arg: 1, scope: !72, file: !1, line: 3, type: !69, flags: DIFlagArtificial)
!76 = !DILocation(line: 3, column: 13, scope: !72)
!77 = !DILocation(line: 0, scope: !72)
!78 = distinct !DISubprogram(name: "init", linkageName: "$s11swift_types7CounterCACycfC", scope: !42, file: !1, line: 3, type: !79, scopeLine: 3, spFlags: DISPFlagDefinition, unit: !0, declaration: !82)
!79 = !DISubroutineType(types: !80)
!80 = !{!42, !81}
!81 = !DICompositeType(tag: DW_TAG_structure_type, name: "$s11swift_types7CounterCXMTD", flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$s11swift_types7CounterCXMTD")
!82 = !DISubprogram(name: "init", linkageName: "$s11swift_types7CounterCACycfC", scope: !42, file: !1, line: 3, type: !79, scopeLine: 3, spFlags: 0)
!83 = !DILocation(line: 0, scope: !78)
!84 = distinct !DISubprogram(name: "init", linkageName: "$s11swift_types7CounterCACycfc", scope: !42, file: !1, line: 3, type: !85, scopeLine: 3, spFlags: DISPFlagDefinition, unit: !0, declaration: !87, retainedNodes: !88)
!85 = !DISubroutineType(types: !86)
!86 = !{!42, !42}
!87 = !DISubprogram(name: "init", linkageName: "$s11swift_types7CounterCACycfc", scope: !42, file: !1, line: 3, type: !85, scopeLine: 3, spFlags: 0)
!88 = !{!89}
!89 = !DILocalVariable(name: "self", arg: 1, scope: !84, file: !1, line: 3, type: !69, flags: DIFlagArtificial)
!90 = !DILocation(line: 3, column: 13, scope: !84)
!91 = !DILocation(line: 0, scope: !84)
!92 = !DILocation(line: 3, column: 27, scope: !93)
!93 = distinct !DILexicalBlock(scope: !94, file: !1, line: 3, column: 27)
!94 = distinct !DILexicalBlock(scope: !84, file: !1, line: 3, column: 21)
!95 = !DILocation(line: 3, column: 38, scope: !96)
!96 = distinct !DILexicalBlock(scope: !94, file: !1, line: 3, column: 38)
!97 = !DILocation(line: 0, scope: !96)
!98 = distinct !DISubprogram(name: "readClass", linkageName: "read_class", scope: !4, file: !1, line: 4, type: !43, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !99)
!99 = !{!100}
!100 = !DILocalVariable(name: "c", arg: 1, scope: !98, file: !1, line: 4, type: !69)
!101 = !DILocation(line: 4, column: 44, scope: !98)
!102 = !DILocation(line: 0, scope: !98)
!103 = !DILocation(line: 5, column: 14, scope: !98)
!104 = !DILocation(line: 5, column: 5, scope: !98)
!105 = distinct !DISubprogram(name: "a.get", linkageName: "$s11swift_types4PairV1as5Int64Vvg", scope: !106, file: !35, type: !107, spFlags: DISPFlagDefinition, unit: !0, declaration: !109)
!106 = !DICompositeType(tag: DW_TAG_structure_type, name: "Pair", scope: !4, file: !1, size: 128, runtimeLang: DW_LANG_Swift, identifier: "$s11swift_types4PairVD")
!107 = !DISubroutineType(types: !108)
!108 = !{!39, !106}
!109 = !DISubprogram(name: "a.get", linkageName: "$s11swift_types4PairV1as5Int64Vvg", scope: !106, file: !35, type: !107, spFlags: 0)
!110 = !DILocation(line: 0, scope: !105)
!111 = distinct !DISubprogram(name: "a.set", linkageName: "$s11swift_types4PairV1as5Int64Vvs", scope: !106, file: !35, type: !112, spFlags: DISPFlagDefinition, unit: !0, declaration: !114)
!112 = !DISubroutineType(types: !113)
!113 = !{!50, !39, !106}
!114 = !DISubprogram(name: "a.set", linkageName: "$s11swift_types4PairV1as5Int64Vvs", scope: !106, file: !35, type: !112, spFlags: 0)
!115 = !DILocation(line: 0, scope: !111)
!116 = distinct !DISubprogram(name: "a.modify", linkageName: "$s11swift_types4PairV1as5Int64VvM", scope: !106, file: !35, type: !117, spFlags: DISPFlagDefinition, unit: !0, declaration: !119)
!117 = !DISubroutineType(types: !118)
!118 = !{!50, !106}
!119 = !DISubprogram(name: "a.modify", linkageName: "$s11swift_types4PairV1as5Int64VvM", scope: !106, file: !35, type: !117, spFlags: 0)
!120 = !DILocation(line: 0, scope: !116)
!121 = distinct !DISubprogram(name: "a.modify", linkageName: "$s11swift_types4PairV1as5Int64VvM.resume.0", scope: !106, file: !35, type: !117, spFlags: DISPFlagDefinition, unit: !0, declaration: !122)
!122 = !DISubprogram(name: "a.modify", linkageName: "$s11swift_types4PairV1as5Int64VvM.resume.0", scope: !106, file: !35, type: !117, spFlags: 0)
!123 = !DILocation(line: 0, scope: !121)
!124 = distinct !DISubprogram(name: "b.get", linkageName: "$s11swift_types4PairV1bs5Int64Vvg", scope: !106, file: !35, type: !107, spFlags: DISPFlagDefinition, unit: !0, declaration: !125)
!125 = !DISubprogram(name: "b.get", linkageName: "$s11swift_types4PairV1bs5Int64Vvg", scope: !106, file: !35, type: !107, spFlags: 0)
!126 = !DILocation(line: 0, scope: !124)
!127 = distinct !DISubprogram(name: "b.set", linkageName: "$s11swift_types4PairV1bs5Int64Vvs", scope: !106, file: !35, type: !112, spFlags: DISPFlagDefinition, unit: !0, declaration: !128)
!128 = !DISubprogram(name: "b.set", linkageName: "$s11swift_types4PairV1bs5Int64Vvs", scope: !106, file: !35, type: !112, spFlags: 0)
!129 = !DILocation(line: 0, scope: !127)
!130 = distinct !DISubprogram(name: "b.modify", linkageName: "$s11swift_types4PairV1bs5Int64VvM", scope: !106, file: !35, type: !117, spFlags: DISPFlagDefinition, unit: !0, declaration: !131)
!131 = !DISubprogram(name: "b.modify", linkageName: "$s11swift_types4PairV1bs5Int64VvM", scope: !106, file: !35, type: !117, spFlags: 0)
!132 = !DILocation(line: 0, scope: !130)
!133 = distinct !DISubprogram(name: "b.modify", linkageName: "$s11swift_types4PairV1bs5Int64VvM.resume.0", scope: !106, file: !35, type: !117, spFlags: DISPFlagDefinition, unit: !0, declaration: !134)
!134 = !DISubprogram(name: "b.modify", linkageName: "$s11swift_types4PairV1bs5Int64VvM.resume.0", scope: !106, file: !35, type: !117, spFlags: 0)
!135 = !DILocation(line: 0, scope: !133)
!136 = distinct !DISubprogram(name: "init", linkageName: "$s11swift_types4PairV1a1bACs5Int64V_AGtcfC", scope: !106, file: !1, line: 7, type: !137, scopeLine: 7, spFlags: DISPFlagDefinition, unit: !0, declaration: !140)
!137 = !DISubroutineType(types: !138)
!138 = !{!106, !39, !39, !139}
!139 = !DICompositeType(tag: DW_TAG_structure_type, name: "$s11swift_types4PairVXMtD", flags: DIFlagFwdDecl, runtimeLang: DW_LANG_Swift, identifier: "$s11swift_types4PairVXMtD")
!140 = !DISubprogram(name: "init", linkageName: "$s11swift_types4PairV1a1bACs5Int64V_AGtcfC", scope: !106, file: !1, line: 7, type: !137, scopeLine: 7, spFlags: 0)
!141 = !DILocation(line: 0, scope: !136)
!142 = distinct !DISubprogram(name: "sumInout", linkageName: "sum_inout", scope: !4, file: !1, line: 8, type: !107, scopeLine: 8, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !143)
!143 = !{!144}
!144 = !DILocalVariable(name: "p", arg: 1, scope: !142, file: !1, line: 8, type: !106)
!145 = !DILocation(line: 8, column: 42, scope: !142)
!146 = !DILocation(line: 0, scope: !142)
!147 = !DILocation(line: 9, column: 14, scope: !142)
!148 = !DILocation(line: 9, column: 20, scope: !142)
!149 = !DILocation(line: 9, column: 16, scope: !142)
!150 = !DILocation(line: 9, column: 5, scope: !142)
!151 = !DILocation(line: 0, scope: !152, inlinedAt: !149)
!152 = distinct !DISubprogram(name: "Swift runtime failure: arithmetic overflow", scope: !35, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagDefinition, unit: !0)
!153 = !DISubroutineType(types: null)
!154 = distinct !DISubprogram(linkageName: "$s11swift_types7CounterCMa", scope: !4, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagDefinition, unit: !0)
!155 = !DILocation(line: 0, scope: !154)
!156 = distinct !DISubprogram(linkageName: "__swift_memcpy16_8", scope: !4, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagDefinition, unit: !0)
!157 = !DILocation(line: 0, scope: !156)
!158 = distinct !DISubprogram(linkageName: "__swift_noop_void_return", scope: !4, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagDefinition, unit: !0)
!159 = !DILocation(line: 0, scope: !158)
!160 = distinct !DISubprogram(linkageName: "$s11swift_types4PairVwet", scope: !4, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !0)
!161 = !DILocation(line: 0, scope: !160)
!162 = distinct !DISubprogram(linkageName: "$s11swift_types4PairVwst", scope: !4, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !0)
!163 = !DILocation(line: 0, scope: !162)
!164 = distinct !DISubprogram(linkageName: "$s11swift_types4PairVMa", scope: !4, file: !35, type: !153, flags: DIFlagArtificial, spFlags: DISPFlagDefinition, unit: !0)
!165 = !DILocation(line: 0, scope: !164)
