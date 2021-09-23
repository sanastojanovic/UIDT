theory mi17131_Milica_Radojicic

imports Complex_Main

begin
text\<open>
  https://www.imo-official.org/problems/IMO2009SL.pdf
  Zadatak: Number theory N4
  Tekst zadatka: Pronaci sve pozitivne cele brojeve n tako da postoji
  niz pozitivnih celih brojeva a1, a2,..., an koji zadovoljava jednacinu
  ak+1 = ((ak)^2 + 1 / ak-1 + 1) - 1 za svako k gde je 2 <= k <= n-1
\<close>

(* Ovakav niz postoji za n = 1, 2, 3, 4 i nijedno drugo n. Posto postojanje ovakvog niza za neko n
  implicira postojanje ovakvog niza za sve brojeve manje od n dovoljno je dokazati da je moguce da
  je n=4 i da nije moguce da je n=5*)


(*Kada je n = 4 moguci primer niza je a1 = 4, a2 = 33, a3 = 217, a4 = 1384*)
lemma
  assumes "(a1::real) = 4" "(a2::real) = 33" "(a3::real) = 217" "(a4::real) = 1384"       
  shows "a3 + 1 = (a2\<^sup>2 + 1) / (a1 + 1)"
proof-
  from assms(1) and assms(2) have "218 = (a2\<^sup>2 + 1) / (a1 + 1)"  by auto
  from this and assms(3) show "a3 + 1 = (a2\<^sup>2 + 1) / (a1 + 1)" by auto
qed
(* ili *)
lemma
  assumes "(a1::real) = 4" "(a2::real) = 33" "(a3::real) = 217" "(a4::real) = 1384"       
  shows "a4 + 1 = (a3\<^sup>2 + 1) / (a2 + 1)"
proof-
  from assms(2) and assms(3) have "1385 = (a3\<^sup>2 + 1) / (a2 + 1)"  by auto
  from this and assms(4) show "a4 + 1 = (a3\<^sup>2 + 1) / (a2 + 1)" by auto
qed

lemma "pomocna1":
  assumes "(a1::nat) > 0" "(a2::nat) > 0"
  assumes "2 dvd a1"
  assumes "2 dvd a2"
  shows "4 dvd (a1 * a2)"
proof -
  from assms(3) have h1: "\<exists> m. a1 = 2 * m" by auto
  then obtain m where "a1 = 2 * m" by blast
  from assms(4) have h2: "\<exists> k. a2 = 2 * k" by auto
  then obtain k where "a2 = 2 * k" by blast
  from this and \<open>a1 = 2 * m\<close> have "a1 * a2 = (2 * m) * (2 * k)" by auto
  then have "a1 * a2 = 4 * m * k" by auto
  then show "4 dvd (a1 * a2)" by auto
qed

lemma "pomocna2":
  assumes "(a2::nat) > 0"
  assumes "a2 mod 2 \<noteq> 0"
  shows "a2\<^sup>2 mod 4 = 1"
proof-
  from assms(2) have "\<exists> m. a2 = (2 * m) + 1" by presburger
  then obtain m where "a2 = (2 * m) + 1" by blast
  then have "a2\<^sup>2 - 1 = ((2*m) + 1)\<^sup>2 - 1" by auto
  then have "a2\<^sup>2 - 1 = 4*m\<^sup>2 + 4*m + 1 - 1" by (simp add: add_mult_distrib2 mult.commute numeral_Bit0)
  then have "a2\<^sup>2 - 1 = 4*(m\<^sup>2 + m)" by auto
  then have "(a2\<^sup>2 - 1) mod 4 = 0" by auto
  then show "a2\<^sup>2 mod 4 = 1" 
       by (smt (z3) \<open>\<And>thesis. (\<And>m. a2 = 2 * m + 1 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> add.commute add_mult_distrib2 mod_mult_self4 mult.commute mult.right_neutral nat_1_add_1 numeral_Bit0 of_bool_eq(2) one_mod_2_pow_eq one_power2 pos2 power2_sum power_mult_distrib)
qed

lemma "a1 is even":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0"
  assumes "a2\<^sup>2 +1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  shows  "(a1 mod 2) =  0"
proof(rule ccontr)
  assume "(a1 mod 2) \<noteq>  0"
  from this have a1po_even: "(a1 + 1) mod 2 = 0"  by presburger
  from this and assms(4) have "(a2\<^sup>2+1) mod 2 = 0" by auto
  then have a2_odd: "a2 mod 2 \<noteq> 0" by (metis even_mod_2_iff even_plus_one_iff even_power pos2)
  then have  "(a2 + 1) mod 2 = 0" by presburger
  from this and assms(5) have "(a3\<^sup>2+1) mod 2 = 0" by auto
  then have a3_odd: "a3 mod 2 \<noteq>  0" by (metis even_mod_2_iff even_plus_one_iff even_power pos2)
  then have "(a3+1) mod 2 = 0" by presburger
  from this and a1po_even and assms(4) have deljivo4: "(a2\<^sup>2 + 1) mod 4 = 0" 
    using pomocna1 add_gr_0 assms(1) assms(3) by presburger
  from a2_odd have "(a2\<^sup>2+1) mod 4 = 2" using pomocna2
    by (metis add.commute assms(2) less_add_same_cancel2 mod_add_right_eq mod_less mult.commute mult.right_neutral mult_2_right numeral_Bit0 zero_less_numeral) 
  from this and deljivo4 show False by auto
qed

lemma "a2 is even":
  assumes "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"
  shows "(a2 mod 2) =  0"
proof(rule ccontr)
  assume "(a2 mod 2) \<noteq>  0"
  from this have a2po_even: "(a2 + 1) mod 2 = 0"  by presburger
  from this and assms(4) have "(a3\<^sup>2+1) mod 2 = 0" by auto
  then have a3_odd: "a3 mod 2 \<noteq> 0" by (metis even_mod_2_iff even_plus_one_iff even_power pos2)
  then have a3po_even: "(a3 + 1) mod 2 = 0"  by presburger
  from this and assms(5) have "(a4\<^sup>2+1) mod 2 = 0" by auto
  then have "a4 mod 2 \<noteq> 0" by (metis even_mod_2_iff even_plus_one_iff even_power pos2)
  then have a4po_even: "(a4 + 1) mod 2 = 0"  by presburger
  from this and a2po_even and assms(4) have deljivo4: "(a3\<^sup>2 + 1) mod 4 = 0" using pomocna1
    by (meson "a1 is even" \<open>a2 mod 2 \<noteq> 0\<close> assms(1) assms(2) assms(3) assms(5))
  from a3_odd have "(a3\<^sup>2+1) mod 4 = 2" using pomocna2
    by (metis add.commute assms(2) less_add_same_cancel2 mod_add_right_eq mod_less mult.commute mult.right_neutral mult_2_right numeral_Bit0 zero_less_numeral) 
  from this and deljivo4 show False by auto
qed

lemma "a3 is even":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows "a3 mod 2 = 0"
proof-
  from assms(6) have h1: "(a3 + 1) dvd (a2\<^sup>2 + 1)" by (metis dvd_triv_left mult.commute)
  from "a2 is even" have h2: "(a2\<^sup>2 + 1) mod 2 \<noteq> 0" 
    by (metis assms(2) assms(3) assms(4) assms(7) assms(8) even_plus_one_iff even_power mod_greater_zero_iff_not_dvd pos2)
  from h1 and h2 have "(a3 + 1) mod 2 \<noteq> 0" by (meson dvd_imp_mod_0 dvd_trans mod_0_imp_dvd)
  then show "a3 mod 2 = 0" by (meson dvd_imp_mod_0 even_plus_one_iff)
qed

lemma "a4 is even":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows "a4 mod 2 = 0"
proof-
  from assms(7) have h1: "(a4 + 1) dvd (a3\<^sup>2 + 1)" by (metis dvd_triv_left mult.commute)
  from "a3 is even" have h2: "(a3\<^sup>2 + 1) mod 2 \<noteq> 0"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) even_plus_one_iff even_power mod_0_imp_dvd pos2)
  from h1 and h2 have "(a4 + 1) mod 2 \<noteq> 0" by (meson dvd_imp_mod_0 dvd_trans mod_0_imp_dvd)
  then show "a4 mod 2 = 0" by (meson dvd_imp_mod_0 even_plus_one_iff)
qed

lemma "a5 is even":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows "a5 mod 2 = 0"
proof-
  from assms(8) have h1: "(a5 + 1) dvd (a4\<^sup>2 + 1)" by (metis dvd_triv_left mult.commute)
  from "a4 is even" have h2: "(a4\<^sup>2 + 1) mod 2 \<noteq> 0"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) even_plus_one_iff even_power mod_0_imp_dvd pos2)
  from h1 and h2 have "(a5 + 1) mod 2 \<noteq> 0" by (meson dvd_imp_mod_0 dvd_trans mod_0_imp_dvd)
  then show "a5 mod 2 = 0" by (meson dvd_imp_mod_0 even_plus_one_iff)
qed

lemma "vieta_add":
  fixes a2::nat
  fixes a2'::nat
  fixes a1::nat
  assumes "(x::nat) > 0"
  assumes "x\<^sup>2 + a1*x + a0 = 0"
  assumes "a2\<^sup>2 + a1*a2 + a0 = 0"
  assumes "a2'\<^sup>2 + a1*a2' + a0 = 0"
  assumes "a1 > 0"
  shows "a2 + a2' = -a1"
proof-
  from assms(2) and assms(3) and assms(4) have "x\<^sup>2 + a1*x + a0 = (x - a2)*(x - a2')"  using assms(2) by force
  then have "x\<^sup>2 + a1*x + a0 = (x\<^sup>2 - x*(a2 + a2') + a2* a2')" using assms(1) assms(2) by auto
  then have "a1*x = (-x*(a2 + a2'))" using assms(2) by fastforce
  then have "(a1*x)/x =  (-x*(a2+a2'))/x" by (metis of_int_of_nat_eq)
  then have "a1 = (-(a2 + a2'))" using assms(1) assms(2) by auto
  then show "a2 + a2' = -a1" using assms(1) assms(5) by auto
qed


lemma "vieta_mul":
  fixes a2::nat
  fixes a2'::nat
  fixes a1::nat
  assumes "(x::nat) > 0"
  assumes "x\<^sup>2 + a1*x + a0 = 0"
  assumes "a2\<^sup>2 + a1*a2 + a0 = 0"
  assumes "a2'\<^sup>2 + a1*a2' + a0 = 0"
  assumes "a1 > 0"
  shows "a2 * a2' = a0"
proof-
  from assms(2) and assms(3) and assms(4) have "x\<^sup>2 + a1*x + a0 = (x - a2)*(x - a2')" using assms(5) by force
  then have "x\<^sup>2 + a1*x + a0 = (x\<^sup>2 - x*(a2 + a2') + a2* a2')" using assms(1) assms(2) by auto
  then have "a0 = (a2 * a2')" using assms(2) by fastforce
  then show "a2 * a2' = a0" by simp 
qed

lemma "jednacina nema resenje":
  assumes "(a2::nat) > 0" "(a3::nat) > 0" "(a2'::nat) > 0" "(a3'::nat) > 0" 
  assumes "a2 mod 2 = 0" "a3 mod 2 = 0" "a2' mod 2 = 0" "a3' mod 2 = 0"
  assumes "a1 = - k*(a3 + 1)"
  assumes "a0 = a3\<^sup>2 - k*(a3 + 1)"
  assumes "x\<^sup>2 + a1*x + a0 = 0"
  assumes "a2\<^sup>2 + a1*a2 + a0 = 0"
  assumes "a2'\<^sup>2+ a1*a2' + a0 = 0"
  assumes "a2 \<ge> a3"
  assumes "a2' \<ge> a3'"
  assumes "a2' + a3' >  a2 + a3"
  assumes "a3' = a3"
  shows False
proof-
  from assms(9) and assms(10) and assms(11) and assms(12) and assms(13) have "a2 + a2' = -a1" using vieta_add by (metis add_is_0 assms(1) less_not_refl2 power_not_zero)
  then have vzbir: "a2 + a2' = k*(a3+1)" using assms(1) by linarith
  from assms(9) and assms(10) and assms(11) and assms(12) and assms(13) have "a2 * a2' = a0" using vieta_mul assms(3) power_not_zero by blast
  then have vproiz: "a2 * a2' = a3\<^sup>2 - k*(a3 + 1)" using assms(1) assms(12) by auto
  have "(a2 + 1)*(a2'+1) = (a2*a2') + (a2 + a2') + 1" by simp
  from this and vzbir and vproiz have "(a2 + 1)*(a2'+1) = a3\<^sup>2 + 1"
    by (metis add_is_0 assms(1) assms(10) assms(12) assms(3) less_numeral_extra(3) nat_0_less_mult_iff)
  then have poc: "(a2' + 1) = (a3\<^sup>2 + 1)/(a2 + 1)" using assms(13) assms(3) by auto
  from assms(14) have "((a3\<^sup>2 + 1)/(a2 + 1)) \<le> ((a3\<^sup>2 + 1)/(a3 + 1))"using assms(13) assms(3) by auto
  then have "((a3\<^sup>2 + 1)/(a3 + 1)) \<le> a3" using assms(13) assms(3) by auto
  from this and assms(14) have "a3 \<le> a2" by auto
  from this and poc have "(a2' + 1) \<le> a2" using \<open>a2 * a2' = a0\<close> assms(11) assms(3) by auto
  then have "a2' < a2" by auto
  from this and assms(17) have "a2' + a3' < a2 + a3" by simp
  from this and assms(16) show False by auto
qed

lemma "glavna":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows False
proof-
  from "a1 is even" have "a1 mod 2 = 0" by (meson assms(1) assms(2) assms(3) assms(6) assms(7))
  from "a2 is even" have "a2 mod 2 = 0" by (meson assms(2) assms(3) assms(4) assms(7) assms(8))
  from "a3 is even" have "a3 mod 2 = 0" by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8))
  from "a4 is even" have "a4 mod 2 = 0" by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8))
  from "a5 is even" have "a5 mod 2 = 0" by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8))
 
  from assms(7) have a2_1:"(a2 + 1) dvd (a3\<^sup>2 + 1)" using dvd_def by blast
  have "(a2\<^sup>2 - 1) = (a2 - 1)*(a2 + 1)"
    by (smt (z3) add.commute add_diff_cancel_left add_mult_distrib2 diff_mult_distrib mult.left_neutral mult.right_neutral power2_eq_square)
  then have a2_2: "(a2 + 1) dvd (a2\<^sup>2 - 1)" by (metis dvd_triv_left mult.commute)
  from a2_1 and a2_2 have "(a2 + 1) dvd ((a3\<^sup>2 + 1) + (a2\<^sup>2 - 1))" using dvd_add_right_iff by blast 
  then have a2po_dvd: "(a2 + 1) dvd (a2\<^sup>2 + a3\<^sup>2)" by (smt (z3) \<open>a2 mod 2 = 0\<close> \<open>a2\<^sup>2 - 1 = (a2 - 1) * (a2 + 1)\<close> add.commute add_diff_inverse_nat assms(2) even_diff_nat even_mult_iff even_plus_one_iff group_cancel.add1 mod_0_imp_dvd mod_less nat_1_add_1 neq0_conv trans_less_add1)
 
  from assms(6) have a3_1: "(a3 + 1) dvd (a2\<^sup>2 + 1)" by (metis dvd_triv_left mult.commute)
  have "(a3\<^sup>2 - 1) = (a3 - 1)*(a3 + 1)" by (smt (z3) diff_add_inverse2 diff_diff_left diff_mult_distrib mult.commute nat_mult_1 power2_eq_square)
  then have a3_2: "(a3 + 1) dvd (a3\<^sup>2 - 1)" by (metis dvd_triv_left mult.commute)
  from a3_1 and a3_2 have "(a3 + 1) dvd ((a2\<^sup>2 + 1) + (a3\<^sup>2 - 1))" using dvd_add_right_iff by blast
  then have a3po_dvd: "(a3 + 1) dvd (a2\<^sup>2 + a3\<^sup>2)" using assms(3) by fastforce

  from "a2 is even" have a2po_odd: "(a2 + 1) mod 2 \<noteq> 0" by (metis \<open>a2 mod 2 = 0\<close> even_plus_one_iff mod_0_imp_dvd)
  from "a3 is even" have a3po_odd: "(a3 + 1) mod 2 \<noteq> 0" by (metis \<open>a3 mod 2 = 0\<close> even_plus_one_iff mod_0_imp_dvd)

  have "\<exists> d. (d dvd (a2 + 1)) \<and> (d dvd (a3 + 1))" by auto
  then obtain d where d_rule:  "(d dvd (a2 + 1))" "(d dvd (a3 + 1))" by blast
  from this and a2po_dvd and a3po_dvd have d1: "d dvd (a2\<^sup>2 + a3\<^sup>2)"by (meson dvd_trans)
  from \<open>d dvd (a2 + 1)\<close> and a2_1 have d2: "d dvd (a3\<^sup>2 + 1)" by (meson dvd_trans)
  from \<open>d dvd (a3 + 1)\<close> and a3_1 have d3: "d dvd (a2\<^sup>2 + 1)" by (meson dvd_trans)
  from d1 and d2 and d3 have "d dvd ((a2\<^sup>2 + 1) + (a3\<^sup>2 + 1) - (a2\<^sup>2 + a3\<^sup>2))" by (meson dvd_add_right_iff dvd_diff_nat)
  then have "d dvd 2" by auto
  from this and a2po_odd and a3po_odd and \<open>(d dvd (a2 + 1))\<close> and \<open>d dvd (a3 + 1)\<close> have d1: "d = 1" by (metis \<open>a3 mod 2 = 0\<close> dvd_add_right_iff dvd_trans mod_0_imp_dvd nat_dvd_1_iff_1)
  from this and a2po_dvd and a3po_dvd and d_rule have "\<exists> k. k * (a2 + 1) * (a3 + 1) = a2\<^sup>2 + a3\<^sup>2" sorry
qed

end