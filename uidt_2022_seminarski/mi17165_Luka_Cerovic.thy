theory mi17165_Luka_Cerovic
  imports
    Main
    Complex_Main

(*

Let S be a finite set, and let A be the set of all functions from S to S. Let f be an
element of A, and let T = f(S) be the image of S under f. Suppose that f \<circ> g \<circ> f \<noteq> g \<circ> f \<circ> g 
for every g in A with g \<noteq> f. Show that f(T) = T

*)

begin

lemma Algebra_A3_IMO2017SL:
  fixes S :: "'a set"
  fixes A :: "('a \<Rightarrow> 'a) set"
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "f \<in> A"
  assumes "T = f ` S"
  assumes "\<forall> g. (g \<in> A \<and> g \<noteq> f \<and> f \<circ> g \<circ> f \<noteq> g \<circ> f \<circ> g)"
  shows "f ` T = T"
  using assms
  by blast

end