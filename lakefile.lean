import Lake
open Lake DSL

package «aoc2023» {
  -- add package configuration options here
}


@[default_target]
lean_exe «day1» {
  root := "day1/Main.lean"
}

lean_exe «day2» {
  root := "day2/Main.lean"
}

lean_exe «day3» {
  root := "day3/Main.lean"
}

lean_exe «day4» {
  root := "day4/Main.lean"
}

lean_exe «day5» {
  root := "day5/Main.lean"
}

lean_exe «day6» {
  root := "day6/Main.lean"
}


lean_exe «day7» {
  root := "day7/Main.lean",

}

lean_exe «day8» {
  root := "day8/Main.lean",

}

lean_exe «day9» {
  root := "day9/Main.lean",

}

lean_exe «day10» {
  root := "day10/Main.lean",

}

lean_exe «day11» {
  root := "day10/Main.lean",

}

-- require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

require std from git "https://github.com/leanprover/std4/"@"v4.3.0"
