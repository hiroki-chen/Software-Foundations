Fixpoint is_even (n: nat): bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S (n')) => is_even n'
  end.

Check is_even 2 = true.

