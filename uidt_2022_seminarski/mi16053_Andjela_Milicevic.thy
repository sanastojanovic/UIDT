theory mi16053_Andjela_Milicevic
  imports Main
begin


(*
   Link https://www.imo-official.org/problems/IMO2019SL.pdf
   Number Theory N2
   Find all triples (a, b, c) of positive integers such that a^3 + b^3 + c^3 = (a*b*c)^2
*)


(* Note that the equation is symmetric. We will assume without loss of generality that a \<ge> b \<ge> c
   and prove that the only solution is (a, b, c) = (3, 2, 1). We will start by proving that c = 1 *)

(* 3*a^3 \<ge> a^3 + b^3 + c^3 > a^3 *)

lemma prva_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  shows "3*a^3 \<ge> a^3 + b^3 + c^3"
  proof -
    from \<open>a \<ge> b\<close> have "3*a^3 \<ge> a^3 + a^3 + b^3" by auto
    from this and \<open>a \<ge> b\<close> have "a^3 + a^3 + b^3 \<ge> a^3 + b^3 + b^3" by auto
    from this and \<open>b \<ge> c\<close> have "a^3 + b^3 + b^3 \<ge> a^3 + b^3 + c^3" by auto
    from this show "3*a^3 \<ge> a^3 + b^3 + c^3"
      by (meson \<open>a ^ 3 + a ^ 3 + b ^ 3 \<le> 3 * a ^ 3\<close> \<open>a ^ 3 + b ^ 3 + b ^ 3 \<le> a ^ 3 + a ^ 3 + b ^ 3\<close> le_trans)
  qed

lemma prva_nejednakost_2:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  shows "a^3 + b^3 + c^3 > a^3"
  proof -
    have "b^3 + c^3 \<ge> 0" by auto
    from this and \<open>b > 0\<close> and \<open>c > 0\<close> have "b^3 + c^3 > 0" by auto
    from this show "a^3 + b^3 + c^3 > a^3" by auto
  qed


(* 3*a^3 \<ge> (a*b*c)^2 > a^3 *)

lemma druga_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "3*a^3 \<ge> (a*b*c)^2" 
  proof -
    from assms(6) and prva_nejednakost_1 show "3*a^3 \<ge> (a*b*c)^2"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5))
  qed

lemma druga_nejednakost_2: 
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "(a*b*c)^2 > a^3" 
  proof -
    from assms(6) and prva_nejednakost_2 show "(a*b*c)^2 > a^3"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5))
  qed


(* 3*a^3 \<ge> a^2 * b^2 * c^2 > a^3 *)
(* 3*a   \<ge>       b^2 * c^2 > a   *)

lemma treca_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "3*a \<ge> b^2 * c^2" 
  proof -
    from druga_nejednakost_1 have "3*a^3 \<ge> (a*b*c)^2"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by presburger
    from this have "3*a^3 \<ge> a^2 * b^2 * c^2"
      by (simp add: power_mult_distrib)
    from this have "3*a*a^2 \<ge> a^2 * b^2 * c^2"
      by (simp add: power2_eq_square power3_eq_cube)
    from this and assms(1) show "3*a \<ge> b^2 * c^2"
      by auto
  qed

lemma treca_nejednakost_2:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "b^2 * c^2 > a"
  proof -
    from druga_nejednakost_2 have "(a*b*c)^2 > a^3"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by presburger
    from this have "a^2 * b^2 * c^2 > a^3"
      by (simp add: power_mult_distrib)
    from this have "a^2 * b^2 * c^2 > a^2*a"
      by (simp add: power2_eq_square power3_eq_cube)
    from this and assms(1) show "b^2 * c^2 > a" 
      by auto
  qed


(* now b^3 + c^3 = a^2 * b^2 * c^2 - a^3         
       b^3 + c^3 = a^2 *(b^2 * c^2 - a)  \<ge> a^2 *)

lemma cetvrta_nejednakost_pomocna:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "a^2 * (b^2 * c^2 - a) \<ge> a^2"
  proof -
    from treca_nejednakost_2 have "b^2 * c^2 - a > 0"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) zero_less_diff by presburger
    from this show "a^2 * (b^2 * c^2 - a) \<ge> a^2"
      by (simp add: Suc_leI)
  qed

lemma cetvrta_nejednakost:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "b^3 + c^3 \<ge> a^2" 
  proof -
    from assms(6) have "a^3 + b^3 + c^3 = a^2 * b^2 * c^2"
      by (simp add: power_mult_distrib)
    from this have "b^3 + c^3 = a^2 * b^2 * c^2 - a^3"
      by auto
    from this have "b^3 + c^3 = a^2 *(b^2 * c^2 - a)"
      by (simp add: mult.assoc power2_eq_square power3_eq_cube right_diff_distrib')
    from this and cetvrta_nejednakost_pomocna show "b^3 + c^3 \<ge> a^2"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by presburger
  qed


(* and so 18*b^3 \<ge> 9*(b^3 + c^3) \<ge> 9*a^2 \<ge> b^4*c^4 \<ge> b^3*c^5 *)

lemma peta_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "18*b^3 \<ge> 9*(b^3 + c^3)"
  proof -
    from assms(5) have "9*b^3 + 9*b^3 \<ge> 9*b^3 + 9*c^3"
      by auto
    from this show "18*b^3 \<ge> 9*(b^3 + c^3)"
      by auto
  qed

lemma peta_nejednakost_2:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "9*(b^3 + c^3) \<ge> 9*a^2"
  proof -
    from cetvrta_nejednakost show "9*(b^3 + c^3) \<ge> 9*a^2"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mult_le_mono2 by presburger
  qed

lemma peta_nejednakost_3:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "9*a^2 \<ge> b^4 * c^4"
  proof -
    have "a^2 = a * a"
      by (simp add: power2_eq_square)
    have "b^4 = b^2 * b^2"
      by auto
    have "c^4 = c^2 * c^2" 
      by auto
    from treca_nejednakost_1 have "3*a \<ge> b^2 * c^2"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by presburger
    from this have "3*a * 3*a \<ge> b^2 * c^2 * b^2 * c^2"
      by (metis (full_types) mult.assoc power2_eq_square power2_nat_le_eq_le)
    from this have "3*a * 3*a \<ge> b^2 * b^2 * c^2 * c^2"
      by (simp add: mult.commute)
    from this and \<open>a^2 = a * a\<close> have "9*a^2 \<ge> b^2 * b^2 * c^2 * c^2"
      by auto
    from this and \<open>b^4 = b^2 * b^2\<close> and \<open>c^4 = c^2 * c^2\<close> show "9*a^2 \<ge> b^4 * c^4"
      by (metis mult.assoc)
  qed

lemma peta_nejednakost_4:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "b^4 * c^4 \<ge> b^3 * c^5"
  proof -
    have "c^5 = c^4 * c"
      by (metis numeral_nat(3) power_Suc2)
    have "b^4 * c^4 = b * b^3 * c^4"
      by (simp add: power3_eq_cube power4_eq_xxxx)
    from this and assms(5) have "b^4 * c^4 \<ge> b^3 * c^4 * c"
      by force 
    from this and \<open>c^5 = c^4 * c\<close> show "b^4 * c^4 \<ge> b^3 * c^5"
      by auto
  qed


(* so 18 \<ge> c^5 which yields c = 1 *)

lemma c_je_jedan:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "c = 1"
  proof - 
    from peta_nejednakost_1 and peta_nejednakost_2 and peta_nejednakost_3 and peta_nejednakost_4
    have "18*b^3 \<ge> b^3 * c^5"
      by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) le_trans)
    from this have "18 \<ge> c^5"
      by (simp add: assms(2))
    from this show "c = 1" 
      sorry
  qed


(* Now, note that we must have a > b, as otherwise we would have 2*b^3 + 1 = b^4 which has no
   positive integer solutions. *)

lemma a_je_strogo_vece_od_b:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  assumes "a = b"
  shows "a > b"
  proof -
    from c_je_jedan have "c = 1"
      using assms(1) assms(3) assms(5) assms(6) assms(7) by blast
    from this and assms(6) have "a^3 + b^3 + 1 = (a*b)^2" 
      by simp
    from this and assms(7) have "b^3 + b^3 + 1 = (b*b)^2"
      by auto
    from this have "2*b^3 + 1 = b^4"
      by (simp add: power2_eq_square power4_eq_xxxx)
    from this have "b^4 - 2*b^3 = 1"
      by auto
    from this have "b^3 * (b - 2) = 1"
      by (metis (no_types, lifting) mult.commute power3_eq_cube power4_eq_xxxx right_diff_distrib')
    from this and assms(2) have "b^3 = 1" by auto
    from this have "b = 1" by auto
    from this and \<open>b^3 * (b - 2) = 1\<close> have "b - 2 = 1" by auto
    from this have "b = 3" by auto
    from this and \<open>b = 1\<close> have False by auto
    from this and assms(4) show "a > b" by auto
  qed


(* So a^3 - b^3 \<ge> (b+1)^3 - b^3 > 1 *)

lemma sesta_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "a^3 - b^3 \<ge> (b+1)^3 - b^3" 
  proof -
    from assms(4) and a_je_strogo_vece_od_b have "a \<ge> b+1"
      by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right assms(2) assms(3) assms(5) assms(6) le_neq_implies_less) 
    from this have "a^3 \<ge> (b+1)^3"
      by auto
    from this show "a^3 - b^3 \<ge> (b+1)^3 - b^3"
      using diff_le_mono by blast
  qed

lemma sesta_nejednakost_2: 
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "(b+1)^3 - b^3 > 1" 
  proof -
    have "(b+1)^3 -b^3 = (b+1) * (b+1)^2 -b^3"
      by (metis mult.commute power2_eq_square power3_eq_cube)
    from this have "(b+1) * (b+1)^2 -b^3 = (b+1) * (b^2 + 2*b +1) -b^3"
      by (metis Suc_eq_plus1 mult_numeral_1_right numeral_One one_power2 plus_nat.simps(2) power2_sum)
    from this have "(b+1) * (b^2 + 2*b +1) -b^3 = b^3 + 2*b^2 + b + b^2 + 2*b + 1 -b^3"
      by (smt (verit, ccfv_SIG) Rings.ring_distribs(2) comm_monoid_mult_class.mult_1 left_add_mult_distrib mult.commute mult_2 power2_eq_square power3_eq_cube)
    from this have "b^3 + 2*b^2 + b + b^2 + 2*b + 1 - b^3 = 3*b^2 + 3*b + 1" by auto
    from this and assms(2) have "3*b^2 + 3*b + 1 > 1" by auto
    from this and assms(2) show "(b+1)^3 - b^3 > 1"
      using \<open>(b + 1) * (b + 1)\<^sup>2 - b ^ 3 = (b + 1) * (b\<^sup>2 + 2 * b + 1) - b ^ 3\<close> \<open>(b + 1) * (b\<^sup>2 + 2 * b + 1) - b ^ 3 = b ^ 3 + 2 * b\<^sup>2 + b + b\<^sup>2 + 2 * b + 1 - b ^ 3\<close>
            \<open>(b + 1) ^ 3 - b ^ 3 = (b + 1) * (b + 1)\<^sup>2 - b ^ 3\<close> \<open>b ^ 3 + 2 * b\<^sup>2 + b + b\<^sup>2 + 2 * b + 1 - b ^ 3 = 3 * b\<^sup>2 + 3 * b + 1\<close> by presburger
  qed


(* and 2*a^3 > 1 + a^3 + b^3 > a^3 *)

lemma sedma_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "2*a^3 > 1 + a^3 + b^3" 
  proof -
    from sesta_nejednakost_1 have "a^3 \<ge> (b+1)^3"
      by (metis One_nat_def Suc_leI a_je_strogo_vece_od_b add.right_neutral add_Suc_right assms(1) assms(3) assms(4) assms(5) assms(6) le_neq_implies_less power_mono zero_le)
    from sesta_nejednakost_2 have "(b+1)^3 > 1 + b^3"
      by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) less_diff_conv)
    from this have "a^3 > 1 + b^3"
      using \<open>(b + 1) ^ 3 \<le> a ^ 3\<close> by linarith
    from this show "2*a^3 > 1 + a^3 + b^3"
      by auto
  qed

lemma sedma_nejednakost_2: 
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "1 + a^3 + b^3 > a^3" 
  proof -
    have "1 + a^3 > a^3" by auto
    from this show "1 + a^3 + b^3 > a^3" by auto
  qed


(* which implies 2*a^3 > a^2 * b^2 > a^3 
   and so        2*a   >       b^2 > a   *)

lemma osma_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "2*a > b^2"
  proof -
    from c_je_jedan have "a^3 + b^3 + 1 = (a*b)^2"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mult.right_neutral power_one)
    from this have "a^3 + b^3 + 1 = a^2 * b^2"
      by (simp add: power_mult_distrib)
    from this and sedma_nejednakost_1 have "2*a^3 > a^2 * b^2"
      by (smt (verit) add.commute assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) group_cancel.add1)
    from this have "2*a * a^2 > a^2 * b^2"
      by (simp add: power2_eq_square power3_eq_cube)
    from this show "2*a > b^2"
      by auto
  qed

lemma osma_nejednakost_2:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "b^2 > a"
  proof -
    from c_je_jedan have "a^3 + b^3 + 1 = (a*b)^2"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mult.right_neutral power_one)
    from this have "a^3 + b^3 + 1 = a^2 * b^2"
      by (simp add: power_mult_distrib)
    from this and sedma_nejednakost_2 have "a^2 * b^2 > a^3"
      by (smt (verit) add.commute assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) group_cancel.add1)
    from this have "a^2 * b^2 > a^2 * a"
      by (simp add: power2_eq_square power3_eq_cube)
    from this show "b^2 > a"
      by auto
  qed


(* Therefore 4*(1 + b^3) = 4*a^2*(b^2 - a) \<ge> 4*a^2 > b^4 *)

lemma deveta_nejednakost_1:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "4*(1 + b^3) \<ge> 4*a^2" 
  proof -
    from c_je_jedan have "a^3 + b^3 + 1 = (a*b)^2"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mult.right_neutral power_one)
    from this have "a^3 + b^3 + 1 = a^2 * b^2"
      by (simp add: power_mult_distrib)
    from this have "1 + b^3 = a^2 * b^2 - a^3"
      by auto
    from this have "1 + b^3 = a^2 * (b^2 - a)"
      by (simp add: power2_eq_square power3_eq_cube right_diff_distrib')
    from this have "4*(1 + b^3) = 4*a^2 * (b^2 - a)"
      by auto
    from this and osma_nejednakost_2 show "4*(1 + b^3) \<ge> 4*a^2" 
      by (metis add.commute assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) c_je_jedan cetvrta_nejednakost mult_le_mono2 power_one)
  qed

lemma deveta_nejednakost_2:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "4*a^2 > b^4" 
  proof -
    from osma_nejednakost_1 have "2*a > b^2"
      using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by presburger
    from this have "2*a * 2*a > b^2 * b^2"
      by (metis mult.assoc power2_eq_square power2_nat_le_eq_le verit_comp_simplify1(3))
    from this show "4*a^2 > b^4"
      by (metis (no_types, opaque_lifting) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double numeral_Bit0 power2_eq_square power_add)
  qed


(* so 4 > b^3*(b-4); that is, b \<le> 4. *)

lemma deseta_nejednakost:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "4 > b^3*(b-4)" 
  proof -
    from deveta_nejednakost_1 and deveta_nejednakost_2 have "4*(1 + b^3) > b^4"
      by (smt (verit, ccfv_threshold) assms(3) assms(4) assms(5) assms(6) le_trans verit_comp_simplify(3))
    from this have "4 + 4*b^3 > b^4" by auto
    from this have "4 > b^4 - 4*b^3" by auto
    from this show "4 > b^3*(b-4)"
      by (simp add: power3_eq_cube power4_eq_xxxx right_diff_distrib')
  qed

lemma jedan:
  assumes "(b::nat) = 1"
  shows "4 > b^3*(b-4)"
  proof -
    from assms show "4 > b^3*(b-4)" by auto
  qed

lemma dva:
  assumes "(b::nat) = 2"
  shows "4 > b^3*(b-4)"
  proof -
    from assms show "4 > b^3*(b-4)" by auto
  qed

lemma tri:
  assumes "(b::nat) = 3"
  shows "4 > b^3*(b-4)"
  proof -
    from assms show "4 > b^3*(b-4)" by auto
  qed

lemma cetiri:
  assumes "(b::nat) = 4"
  shows "4 > b^3*(b-4)"
  proof -
    from assms show "4 > b^3*(b-4)" by auto
  qed

lemma pet:
  assumes "(b::nat) = 5"
  assumes "4 > b^3*(b-4)"
  shows False
  proof -
    from assms(1) have "4 < b^3*(b-4)" by auto
    from this and assms(2) show False  by auto
  qed


(* Now, for each possible value of b with 2 \<le> b \<le> 4 we obtain a cubic equation for a with
   constant coefficients. These are as follows:

                b = 2:  a^3 - 4*a^2 + 9  = 0
                b = 3:  a^3 - 9*a^2 + 28 = 0
                b = 4:  a^3 -16*a^2 + 65 = 0

   The only case with an integer solution for a with b \<le> a is b = 2, leading to (a, b, c) = (3, 2, 1) *)

lemma prva_jednacina:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  assumes "b = 2" 
  shows "a^3 + 9 - 4*a^2 = 0"
  proof -
    from c_je_jedan have "a^3 + b^3 + 1 = a^2 * b^2"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) nat_mult_1_right power_mult_distrib power_one)
    from assms(7) have "a^3 + 8 + 1 = a^2 * 4"
      using \<open>a ^ 3 + b ^ 3 + 1 = a\<^sup>2 * b\<^sup>2\<close> by force
    from this have "a^3 + 9 = 4*a^2"
      by presburger
    from this show "a^3 + 9 - 4*a^2 = 0"
      by fastforce
  qed

lemma druga_jednacina:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  assumes "b = 3" 
  shows "a^3 + 28 - 9*a^2 = 0"
  sorry

lemma treca_jednacina:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  assumes "b = 4" 
  shows "a^3 + 65 - 16*a^2 = 0"
  sorry

lemma resenje:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a \<ge> b" "b \<ge> c" 
  assumes "a^3 + b^3 + c^3 = (a*b*c)^2"
  shows "a = 3 \<and> b = 2 \<and> c = 1"
  sorry

end
