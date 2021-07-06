theory mi17259_Lazar_Celikovic
  imports Main Complex_Main HOL.Set "HOL-Library.Infinite_Set"
begin

text \<open>

link: https://imomath.com/srb/zadaci/2008_mmo.pdf
Algebra, zadatak 2

(a) Dokazati da je
    x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 \<ge> 1
    za sve realne brojeve x, y i z takve da je svaki od njih
    razlicit od 1 i da vazi x*y*z = 1

(b) Dokazati da se jednakost dostize za beskonacno mnogo trojki
    racionalnih brojeva x, y i z za koje vazi da je svaka
    koordinata razlicita od 1 i da je proizvod 

\<close>

lemma deo_pod_a:
  fixes x y z :: "real"
  assumes "x \<noteq> 1" "y \<noteq> 1" "z \<noteq> 1" "x * y * z = 1"
  shows "(x^2 / (x - 1)^2) + 
         (y^2 / (y - 1)^2) + 
         (z^2 / (z - 1)^2) \<ge> 1"
  using assms
  sorry

definition jedno_resenje :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
"jedno_resenje x y z = (x \<noteq> 1 \<and> 
                        y \<noteq> 1 \<and> 
                        z \<noteq> 1 \<and> 
                        x * y * z = 1 \<and>
                        ((x^2 / (x - 1)^2) + 
                         (y^2 / (y - 1)^2) + 
                         (z^2 / (z - 1)^2) = 1))"

(*Ovde je problem jer na znam kako da kazem ovo 
  x iz rat, y iz rat, z iz rat pa vazi resenje x y z
*)

(*Ovo sto napisah ovde verovatno nema veze sa zivotom*)
lemma deo_pod_b:
  fixes x y z :: "rat"
  shows "infinite {resenje x y z}"
  unfolding jedno_resenje_def
  sorry

end