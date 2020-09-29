theory mi16136_Krizan_Andjela
  imports Complex_Main
begin

text \<open>
Zadatak 4, drugi razred sa linka: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf
Tekst:
Ako su m i n prirodni brojevi za koje vazi 7*m^2 + 7*m + 2 = n^2,
dokazati da je broj n + 1 jednak zbiru kvadrata dva uzastopna prirodna broja.
\<close>

(* jasno mi je zasto mi nije potrebna ali malo uprostava resenje pa nek ostane *)
lemma p1:
  fixes m n :: nat
  assumes "7*m^2 + 7*m + 2 = n^2"
  shows "7*(2*m+1)^2 = (2*n-1)*(2*n+1)"
proof-
  have "7*(4*m^2 + 4*m + 1) + 1 = 4*n^2"
    using assms by auto
  
  also have "7*(4*m^2 + 4*m + 1) = 4*n^2 - 1"
    using \<open>7 * (4 * m\<^sup>2 + 4 * m + 1) + 1 = 4 * n\<^sup>2\<close> by linarith
 
  also have "7*(2*m+1)^2 = 4*n^2 -1 "
    by (smt \<open>7 * (4 * m\<^sup>2 + 4 * m + 1) = 4 * n\<^sup>2 - 1\<close> add.assoc add.commute mult.commute mult.left_commute mult_2 nat_mult_1_right numeral_Bit0 one_power2 power2_sum power_mult_distrib)
  
  finally show ?thesis
    by (smt Nat.diff_cancel \<open>7 * (2 * m + 1)\<^sup>2 = 4 * n\<^sup>2 - 1\<close> add.commute add_mult_distrib2 diff_mult_distrib mult.commute mult_2 nat_mult_1 numeral_Bit0 power2_eq_square) 
qed

(* ne znam kako da dokazem zato sto mi treba da b bude int - u nat brojevima 0 - 2 = 0 a meni treba -2*)
lemma mod_pom:
  fixes b :: nat
  assumes "b > 0"
  shows "(7*b^2 - 2) mod 7 = 5"
proof (induction b)
  case 0
   have "(7*0^2 -(2::int)) mod 7 = (-2) mod 7"
      by auto
   then have "(-2) mod (7::int) = 5"
     by auto
  then show ?case 
    sorry
next
  case (Suc b)
  then show ?case sorry
qed


(* ovo mi ni u resenju nije najjasnije zasto je tako*)
lemma mod_rez:
  fixes a :: nat
  assumes "a^2 mod 7 = 5"
  shows "False"
  sorry
  

lemma kontradikcija:
  fixes m n a b :: nat
  assumes "a^2=2*n-1" "7*b^2 = 2*n+1" "b > 0"
  shows "False"
proof-
  have "7*b^2 - a^2 = 2*n + 1 - (2*n - 1)" 
    using assms by simp
  then have "7*b^2 - a^2 = 2"
        by (metis Nat.add_diff_assoc2 Suc_1 Suc_inject add_2_eq_Suc' add_Suc_right assms(2) diff_diff_cancel diff_le_self le_Suc_eq le_add2 nat_1_eq_mult_iff numeral_eq_one_iff semiring_norm(86))
  then have "a^2 = 7*b^2 - 2"
    by auto
  then have "a^2 mod 7 = (7*b^2 - 2) mod 7"
    by auto
  then have "a^2 mod 7 = 5"
    using mod_pom
    by (simp add: assms(3))
  then show ?thesis
    using mod_rez
    by blast
  qed


lemma p3:
  fixes m n a b k :: nat
  assumes "a^2=2*n+1" "7*b^2 = 2*n - 1" "a = 2*k + 1"
  shows "n + 1 = k^2 + (k+1)^2"
proof-
   have "2*n + 1 = 4*k^2 + 4*k + 1"
    by (smt ab_semigroup_add_class.add_ac(1) add.commute assms(1) assms(3) mult_2 mult_numeral_left_semiring_numeral numeral_Bit0 numeral_times_numeral one_add_one one_power2 power2_sum power_mult_distrib)

  also have "n = 2*k^2 + 2*k"
    using \<open>2 * n + 1 = 4 * k\<^sup>2 + 4 * k + 1\<close> by auto
 
  also have "n+1 = 2*k^2 + 2*k +1"
    by (simp add: \<open>n = 2 * k\<^sup>2 + 2 * k\<close>)

   show ?thesis
    by (smt \<open>n + 1 = 2 * k\<^sup>2 + 2 * k + 1\<close> ab_semigroup_add_class.add_ac(1) add.commute mult_2 mult_numeral_1_right numeral_One one_power2 power2_sum)

qed

(* ni iz resenja zadatka mi nije najjasnije zasto ovo vazi, pa ne znam kako da dokazem *)
lemma p4:
  fixes m n a b :: nat
  assumes "7*(2*m+1)^2 = (2*n-1)*(2*n+1)"
  shows "2*n-1 = a^2 \<and> 2*n+1 = 7*b^2 \<or> 2*n+1 = a^2 \<and> 2*n-1 = 7*b^2"
    sorry
  

lemma zadatak:
  fixes m n a b :: nat
  assumes "7*m^2 + 7*m + 2 = n^2" "b > 0" 
  shows "\<exists> a b. b = a + 1 \<and> n + 1 = a^2 + b^2"
proof-
  have "2*n-1 = a^2 \<and> 2*n+1 = 7*b^2 \<or> 2*n+1 = a^2 \<and> 2*n-1 = 7*b^2"
    using p4
    using assms p1 by blast
  then have "2*n+1 = a^2 \<and> 2*n-1 = 7*b^2"
    using kontradikcija
    by (metis assms(2))
  then have "n + 1 = k^2 + (k+1)^2"
    using p3
    by (smt assms p1 p4)
  then show ?thesis
    by blast
qed  
end