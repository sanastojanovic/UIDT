theory mi16196_Sanja_Mijatovic

imports Main Complex_Main

begin

text \<open>

Link: https://www.imo-official.org/problems/IMO2020SL.pdf
Algebra A3

Suppose that a, b, c, d are positive real numbers satisfying (a+c) * (b+d) = a*c + b*d.
Find the smallest possible value of a/b + b/c + c/d + d/a.

Answer: The smallest possible value is 8.

\<close>

section \<open>Prvi seminarski\<close>

(* S = a/b + b/c + c/d + d/a
Potrebno je da pokazemo da je S \<ge> 8
 *)
lemma task1:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  shows "a/b + b/c + c/d + d/a \<ge> 8"
  using assms
  sorry

(* Kada dokazemo da je S \<ge> 8, potrebno je da odredimo a, b, c i d,
   takve da je a/b + b/c + c/d + d/a = 8 i time pokazemo da je 8 najmanja vrednost. *)
lemma task2:
  fixes a b c d :: real
  shows "\<exists> a b c d. a/b + b/c + c/d + d/a = 8 \<and> (a + c) * (b + d) = a*c + b*d \<and>
  a > 0 \<and> b > 0 \<and> c > 0 \<and> d > 0"
  sorry
