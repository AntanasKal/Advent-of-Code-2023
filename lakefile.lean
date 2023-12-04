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
