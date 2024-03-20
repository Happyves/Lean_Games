

example : True :=
  by
  let f := fun n : Nat => if n / 3 = 5 then 1 else 0
  let f15 := f 15
  --rw [f] at f15
  --dsimp [f] at f15
  --unfold f at f15
  rw [if_pos _] at f15


example : True :=
  by
  let f := fun n : Nat => if n / 3 = 5 then 1 else 0
  let f15 := f 15
  have h15 : f15 = f 15 := rfl
  dsimp [f] at h15
  have h152 : f15 = if _ then _ else _ := rfl
  rw [if_pos _] at h152
