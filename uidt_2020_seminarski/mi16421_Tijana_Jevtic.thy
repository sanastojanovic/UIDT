(*
  Seminarski
  Tijana Jevtić, mi16421
*)

theory mi16421_Tijana_Jevtic
  imports Main Complex_Main
begin

section "Prvi seminarski"
text 
  \<open> 
  Prvi razred, zadatak 1 - link: https://imomath.com/srb/zadaci/RS_2009_republicko_resenja.pdf
  
  Neka su a, b, c pozitivni brojevi. Dokazati da iz a^2 + b^2 = c^2 slijedi
  (a^2 + (c − b)^2) / (b^2 + (c − a)^2) = (c − b) / (c − a)
  Da li vazi obrnuto tvrdjenje?    
  \<close>

lemma kvadrat_binoma:
  fixes a b :: real
  assumes "a > 0" "b > 0"
  shows "(a-b)^2 = a^2 - 2*a*b + b^2"
  by (simp add: power2_diff)

lemma gornji_deo: 
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a^2 + b^2 = c^2"
  shows "a^2 + (c-b)^2 = 2*c*(c - b)"
proof-
  have "a^2 + (c-b)^2 = a^2 + c^2 - 2*b*c + b^2"
    by (simp add: power2_diff)
  also have "... =  c^2 - b^2 + c^2 - 2*b*c + b^2"
    using assms(4) by auto
  also have "... = c^2 + c^2 - 2*b*c"
    by auto
  also have "... = 2*c^2 - 2*b*c"
    by auto
  also have "... = 2 * (c^2 - b*c)"
    by auto
  also have "... = 2*c * (c - b)"
  by (simp add: left_diff_distrib mult.commute power2_eq_square)
  finally show ?thesis
    .
qed

lemma donji_deo:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a^2 + b^2 = c^2"
  shows "b^2 + (c-a)^2 = 2*c*(c - a)"
  proof-
  have "b^2 + (c-a)^2 = b^2 + c^2 - 2*a*c + a^2"
    by (simp add: power2_diff)
  also have "... =  c^2 - a^2 + c^2 - 2*a*c + a^2"
    using assms(4) by auto
  also have "... = c^2 + c^2 - 2*a*c"
    by auto
  also have "... = 2*c^2 - 2*a*c"
    by auto
  also have "... = 2 * (c^2 - a*c)"
    by auto
  also have "... = 2*c * (c - a)"
    by (simp add: left_diff_distrib mult.commute power2_eq_square)
  finally show ?thesis
    .
qed

lemma levo_ka_desno:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a^2 + b^2 = c^2"
  shows "(a^2 + (c-b)^2) / (b^2 + (c-a)^2) = (c-b) / (c-a)"
proof-
  have "(a^2 + (c-b)^2) / (b^2 + (c-a)^2) = (2*c*(c - b)) / (2*c*(c - a))"
    by (simp add: donji_deo gornji_deo assms(1) assms(2) assms(3) assms(4))
  also have "... =  (c-b) / (c-a)"
  using assms(3) by auto
  finally show ?thesis
    .
qed

text \<open> Pretpostavimo suprotno. \<close>
lemma desno_ka_levo:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "(a^2 + (c-b)^2) / (b^2 + (c-a)^2) = (c-b) / (c-a)"
  shows "a^2 + b^2 \<noteq> c^2"
  sorry

lemma kontraprimer:
  fixes a b c :: real
  assumes "a = 1" "b = 1" "c = 2" "(a^2 + (c-b)^2) / (b^2 + (c-a)^2) = (c-b) / (c-a)"
  shows "a^2 + b^2 \<noteq> c^2"
  by (simp add: assms(1) assms(2) assms(3))

end