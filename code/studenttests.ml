open Assert

let student_reg_alloc_tests =
  [
    ( "trieharder.oat",
      "",
      "YESNO0" );
  ]

let oat_regalloc_quality_tests = student_reg_alloc_tests

let provided_tests : suite =
  [
    Test
      ( "[Student provided tests] reg alloc correctness tests",
        GradedTests.pass_all_executed_oat_file oat_regalloc_quality_tests );
    Test
      ( "[Student provided tests] reg alloc quality tests",
        quality_oat oat_regalloc_quality_tests );
  ]

