

example : True :=
  by
  let f := fun n : Nat => if n / 3 = 5 then 1 else 0
  let f15 := f 15
  --rw [f] at f15
  --dsimp [f] at f15
  --unfold f at f15
  rw [if_pos _] at f15
