theory mi15403_Marko_Stankovic
  imports Main HOL.Real
begin

text ‹Seminarski
Suppose that a sequence a1, a2, . . . of positive real numbers satisfies
a(k+1) ≥ (k * a (k) / ((a(k))^2 + (k - 1)), k ≥ 1 for every positive integer k.
Prove that a1 + a2 + ... + an ≥ n for every n ≥ 2.
›

(* Lema (2) u dokazu, nakon koje bi trebalo primeniti AM_GM nejednakost *)
(* a1 + a2 + ... + am ≥ m / a(m+1)*)

(*
lemma middle_step_lemma:
  fixes theList :: "real list" and n :: "nat" and m :: "nat"
  assumes "n ≥ 3"
  assumes "m ∈ (set [2 .. n-2])"
  assumes "length theList = n"
  assumes "∀ x. x ∈ (set theList) ⟶ x > 0"
  assumes "k ∈ (set [1 .. n-1])"
  assumes "(theList ! (k+1)) ≥ (k * (theList ! k)) / ((theList ! k)⇧2 + k - 1)"
  assumes "k / (theList ! (k + 1)) - (k - 1) / (theList ! k) ≤ theList ! k"
  shows "m / (theList ! (m + 1)) ≤ (∑ i ← [1..m]. theList ! i)"

  sorry

*)



lemma AM_GM_Inequality:
  fixes l :: "real list" and n :: "nat"
  assumes "length l = n"
  assumes "∀ el. el ∈ (set l) ⟶ el > 0"
  shows "(sum_list l) / n ≥ (root (∏ el ← l. el))"
  sorry

theorem Algebra_A1_IMO2015:
  fixes sequence :: "real list" and n :: "nat"
  assumes "length sequence = n"
  assumes "∀ x. x ∈ (set sequence) ⟶ x > 0"
  assumes "k ∈ (set [1 .. n-1])"
  assumes "sequence ! (k+1) ≥ (k * (sequence ! k)) / ((sequence ! k)⇧2 + k - 1)"
  assumes "n ≥ 2"
  shows "sum_list sequence ≥ n"
  using assms
  sorry

(*
proof-
  have "(k / (sequence ! (k + 1))) ≤ ((sequence ! k) + (k - 1)/(sequence ! k))"
    sorry
  then have "k / (sequence ! (k + 1)) - (k - 1) / (sequence ! k) ≤ sequence ! k"
    by simp
  sorry
qed
*)






text ‹
Testiranje
›

value "sum_list [0..<5]"

value "length [1, 2, 3::nat, 5]"

abbreviation aList :: "nat list" where 
"aList ≡ [1::nat, 2, 412, 3, 25, 123]"

value "aList ! 5"

abbreviation bList :: "real list" where
"bList ≡ [1::real, 15, 123.3]"

value "aList ! 5"

value "length aList"

value "Cons aList"

value "root 4::nat"

(* value "∑ k ∈ {1.. n} ak" *)


value "∑ k ← [1..3]. k"

value "∏ i ← [1..5] . i"

value "∏ i ← [1, 5::nat, 6] . i"

end