theory mi16167_Matija_Sreckovic
  imports Main HOL.Real

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2021SL.pdf
Algebra A5
\<close>

(* liste krecu od 0, a u zadatku krecu od 1 *)
lemma
  fixes a::"real list" and n::"nat"
  assumes "n \<ge> 2"
  assumes "length a = n"
  assumes "\<forall> x. x \<in> (set a) \<longrightarrow> x > 0"
  assumes "(sum_list a) = 1"
  shows "(\<Sum>k\<leftarrow>[0..<n]. ( ((a!k) / (1-(a!k))) * (\<Sum>i\<leftarrow>[1..<(k-1)]. (a!i))\<^sup>2 )) < ((1::real)/3)"
  sorry


(* playground *)

value "\<Sum>k\<leftarrow>[0..<3]. ( \<Sum>i\<leftarrow>[0..<(k-1)]. ([1::real,2, 3]!i) )"

value "[1::real, 15, 123.3]!k"

value "\<Sum>k\<leftarrow>[0..<3]. [1::real, 2, 3]!k"

value "[1..<4]!2" (* \<rightarrow> [1, 2, 3] *)

find_consts "nat \<Rightarrow> nat \<Rightarrow> nat list"

end