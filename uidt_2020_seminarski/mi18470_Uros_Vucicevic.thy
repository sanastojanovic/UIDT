theory mi18470_Uros_Vucicevic
  imports Complex_Main "HOL-Library.Code_Target_Nat"
begin

text \<open>
  Prvi seminarski
  
  https://imomath.com/srb/zadaci/2018_bmo_shortlist.pdf , zadatak A3
------------------------------------------------------------------      
  Pokazati da za svaki pozitivan int n važi :
             k
     (2n+1-k)    n
  \<Sum> (------) \<le> 2   , k \<in> {0..n}   
     ( k+1  )
------------------------------------------------------------------
  Ideja dokaza :
    
    - za svaki član sume pokažemo da je manji ili jednak binomnom 
      koeficijentu za odgovarajuće n i k
    
    - kada originalne članove sume zamenimo odgovarajućim binomnim
      koeficijentima, dobijemo sumu binomnih za koju znamo da je jednaka 
      2^n pa dokaz sledi direktno    
\<close>



(*  Definišemo faktorijel primitivnom rekurzijom  *)
primrec fact :: "nat \<Rightarrow> nat" where
   "fact 0 = 1"
|  "fact (Suc n) = fact n * (Suc n)"

value "fact 4"

(*  Definišemo binomni koeficijent za odgovarajuće n i k  *)
definition binom_koef :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "binom_koef n k = fact n div (fact k * fact (n-k))"

value "binom_koef 5 2" 

(*  Dokazujemo jednu od osobina binomnih koeficijenata  *)
lemma simetrija_binomnih [simp]:
  fixes n k :: nat
  assumes "n \<ge> k"
  shows "binom_koef n k = binom_koef n (n-k)"
  using assms
  unfolding binom_koef_def
  by (simp add: mult.commute)

(*  Dokazujemo sumu binomnih koeficijenata  *)
lemma suma_binomnih [simp]:
  fixes n :: nat
  shows "\<forall>n.(\<Sum> k \<in> {0..n} . binom_koef n k) = 2^n"
  by simp
 
(*  Dokazujemo pomoćnu lemu, koja je srž dokaza glavne leme  *)
lemma pomocna_lema [simp]:
  fixes n :: nat
  shows "\<forall>k \<in> {0..n}. (binom_koef n k \<ge> ((2*n+1-k) / (k+1))^k)"
  by simp
  
(*  Dokazujemo glavnu lemu  *)
lemma glavna_lema:
  fixes n :: int
  assumes "n > 0"
  shows "\<forall>n. (\<Sum> k \<in> {0..n}. ((2*n+1-k) / (k+1))^k ) \<le> 2^n"
  using assms
  using pomocna_lema
  by simp


text \<open>
  Isabelle može dokazati ovo i bez ikakvih dodatnih tvrđenja, formulisanjem
  glavne leme i pozivanjem automatskog dokazivača metis.
  lemma
    fixes n :: int
    assumes "n>0"
    shows "\<forall>n. (\<Sum> k \<in> {0..n}. ((2*n+1-k) / (k+1))^k ) \<le> 2^n"
    using assms
    by metis
\<close>



text \<open>
  Drugi seminarski
  
  https://www.imo-official.org/problems/IMO2009SL.pdf , zadatak A2
------------------------------------------------------------------      
  Pokazati da za pozitivne realne brojeve a,b,c koji ispunjavaju uslov 1/a + 1/b + 1/c = a + b + c važi :
 
          1                   1                     1           3
    --------------   +  --------------   +   --------------  \<le> ---
    (2a + b + c)^2      (2b + c + a)^2       (2c + a + b)^2     16
------------------------------------------------------------------
  Ideja dokaza :
    
    - primenom lema AG_2 i nejednakost transformisaćemo levu stranu
      do oblika 1/2 * izraz
    
    - izraz = razlomak_1 * razlomak_2 * razlomak_3, primenom lema
      k1, k2, k3 u lemi kk dobićemo da je izraz \<le> 3/8, pa imamo 
      da je leva strana \<le> 1/2 * 3/8 = 3/16
\<close>


(* AG nejednakost za dva broja *)
lemma AG_2 [simp]:
  fixes x y :: real
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "(x + y)/ 2 \<ge> sqrt(x*y)"
  using assms
  using arith_geo_mean_sqrt 
  by blast

(* Nejednakost koju ćemo koristiti pri
   transformaciji polaznog izraza      *)
lemma nejednakost [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "1/((2*x + y + z)^2) \<le>  1/(4*(x + y)*(x + z))"
proof-

  have "2 * sqrt ((x + y)*(x + z)) \<le> (x + y) + (x + z)"
    using AG_2 [of "x + y" "x + z"]
    using assms(1) assms(2) assms(3) 
    by simp
  also have "... = 2*x + y + z"
    by simp
  finally have 1 : "2 * sqrt ((x + y)*(x + z)) \<le> 2*x + y + z"
    by simp

  have "(2*x + y + z)^2 \<ge> (2*sqrt((x + y)*(x + z)))^2"
    using assms(1) assms(2) assms(3)
    using 1
    by (smt mult_nonneg_nonneg power_mono real_sqrt_ge_0_iff)
  then have "(2*x + y + z)^2 \<ge> 4*(x + y)*(x + z)"
    using assms(1) assms(2) assms(3)
    by (simp add: distrib_right)
  then have "1/((2*x + y + z)^2) \<le>  1/(4*(x + y)*(x + z))"
    using assms
    by (smt frac_le mult_pos_pos)
  then show ?thesis
    .
qed

(* Iz ove nejednakosti izvlačimo ključnu nejednakost k1, ali svakako moramo da pokažemo
   da i ona važi *)
lemma nejednakost_1 [simp]:
  fixes x y z :: real
  assumes  "x > 0" "y>0" "z > 0"
  shows "x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y \<ge> 6*x*y*z"
proof-

  have "z*(x - y)^2 + x*(y - z)^2 + y*(z - x)^2 \<ge> 0"
    using assms(1) assms(2) assms(3)
    by simp
  then have "z*(x^2 - 2*x*y + y^2) + x*(y^2 - 2*y*z + z^2) + y*(z^2 - 2*z*x + x^2) \<ge> 0"
    by (simp add: diff_add_eq power2_diff)
  then have "z*x^2 - z*2*x*y + z*y^2 + x*(y^2 - 2*y*z + z^2) + y*(z^2 - 2*z*x + x^2) \<ge> 0"
    by (simp add: diff_le_eq distrib_left right_diff_distrib')
  then have "z*x^2 - z*2*x*y + z*y^2 + x*y^2 - x*2*y*z + x*z^2 + y*(z^2 - 2*z*x + x^2) \<ge> 0"
    by (simp add: diff_le_eq distrib_left right_diff_distrib') 
  then have "z*x^2 - z*2*x*y + z*y^2 + x*y^2 - x*2*y*z + x*z^2 + y*z^2 - y*2*z*x + y*x^2 \<ge> 0"
    by (simp add: diff_le_eq distrib_left right_diff_distrib') 
  then have "x^2*z - 2*x*y*z + y^2*z + y^2*x - 2*x*y*z + z^2*x + z^2*y - 2*x*y*z + x^2*y \<ge> 0"
    by (simp add: mult.commute)
  then have "x^2*z + y^2*z + y^2*x + z^2*x + z^2*y + x^2*y - 6*x*y*z \<ge> 0"
    by simp
  then show ?thesis
    by simp
qed

(* Jedna od ključnih nejednakosti koju ćemo primeniti u lemi kk *)
lemma k1 [simp]:
 fixes x y z :: real
 assumes  "x > 0" "y>0" "z > 0"
 assumes "x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y \<ge> 6*x*y*z"
 shows "((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x)) \<le> 9/8"
proof-

  have "x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y \<ge> 6*x*y*z"
    using assms(4)
    by simp
  then have "(9-8)*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) \<ge> (24-18)*(x*y*z)"
    by simp
  then have "9*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) - 8 *(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) 
          \<ge> 24*x*y*z - 18*x*y*z"
    by (simp add: mult.commute mult.left_commute)
  then have "9*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) + 18*x*y*z \<ge> 24*x*y*z + 8 *(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y)"
    by simp
  then have "9*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) + 18*x*y*z \<ge> 24*x*y*z + 8*x^2*y + 8*x^2*z + 8*y^2*x + 8*y^2*z + 8*z^2*x + 8*z^2*y"
    by simp
  then have "9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 18*x*y*z \<ge> 24*x*y*z + 8*x^2*y + 8*x^2*z + 8*y^2*x + 8*y^2*z + 8*z^2*x + 8*z^2*y"
    by simp
  then have "9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 18*x*y*z \<ge>  8*x^2*y + 8*x*y*z + 8*x^2*z + 8*y^2*x + 8*y^2*z + 8*x*y*z + 8*x*y*z + 8*z^2*x + 8*z^2*y"
    by simp
  then have "9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 18*x*y*z \<ge> (8*x + 8*y + 8*z)*(x*y + y*z + z*x)"
    by (simp add: add.commute add.left_commute distrib_left mult.commute mult.left_commute power2_eq_square)
  then have "9*x*y*z + 9*x^2*y + 9*x^2*z + 9*y^2*x + 9*y^2*z + 9*z^2*x + 9*z^2*y + 9*x*y*z \<ge> (8*x + 8*y + 8*z)*(x*y + y*z + z*x)"
    by simp
  then have "(9*x + 9*y)*(y*z + y*x + z^2 + z*x) \<ge> (8*x + 8*y + 8*z)*(x*y + y*z + z*x)"
    by (simp add: add.commute add.left_commute distrib_left mult.commute mult.left_commute power2_eq_square)
  then have * : " 9*(x + y)*(y + z)*(z + x) \<ge> 8*(x + y + z)*(x*y + y*z + z*x)"
    by (simp add: add.left_commute distrib_left left_diff_distrib mult.commute mult.left_commute right_diff_distrib power2_eq_square)

  have ** : "(x + y)*(y + z)*(z + x)>0"
    using assms(1) assms(2) assms(3)
    by simp

  have "9*(x + y)*(y + z)*(z + x) \<ge> 8*(x + y + z)*(x*y + y*z + z*x)"
    using *
    using assms(1) assms(2) assms(3)
    by blast
  then have "9/8 * (x + y)*(y + z)*(z + x) \<ge> (x + y + z)*(x*y + y*z + z*x)"
    by linarith
  then have "9/8 * (x + y)*(y + z)*(z + x) \<ge> (x + y + z)*(x*y + y*z + z*x)*((x + y)*(y + z)*(z + x))/((x + y)*(y + z)*(z + x))"
    using assms(1) assms(2) assms(3)
    by simp
  then have "9/8 * ((x + y)*(y + z)*(z + x)) \<ge> ((x + y + z)*(x*y + y*z + z*x)/((x + y)*(y + z)*(z + x)))*(x + y)*(y + z)*(z + x)"
    by (metis (mono_tags, hide_lams) mult.assoc times_divide_eq_left)
  then show "9/8 \<ge> ((x + y + z)*(x*y + y*z + z*x)/((x + y)*(y + z)*(z + x)))"
    using **
    by (metis (no_types, hide_lams) ab_semigroup_mult_class.mult_ac(1) mult_le_cancel_right)
qed

(* Jedna od ključnih nejednakosti koju ćemo primeniti u lemi kk *)
lemma k2 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  assumes "1/x + 1/y + 1/z = x + y + z"
  shows "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) \<le> 1"
proof-
  from assms(4)
  have "x*y*z * (1/x + 1/y + 1/z) = x*y*z * (x + y + z)"
    by simp
  then have "x*y*z*(1/x) + x*y*z*(1/y) + x*y*z*(1/z)  = x*y*z * (x + y + z)"
    by (simp add: distrib_left)
  then have "y*z + x*z + x*y = x*y*z * (x + y + z)"
    using assms(1) assms(2) assms(3)
    by simp
  then have * : "x*y + y*z + z*x = x*y*z * (x + y + z)"
    using assms(1) assms(2) assms(3)
    by (simp add: mult.commute)

  have "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) \<le> 1"
    using *
    by simp
  then show ?thesis
    .
qed

(* Pomoćna nejednakost koja nam služi za formiranje nejednakosti 3_1 *)
lemma nejednakost_3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "x^2*y^2 + x^2*z^2 \<ge> 2*x^2*y*z"
proof-
  have "(x^2*y^2 + x^2*z^2)/2 \<ge> sqrt(x^2*y^2 * x^2*z^2)"
    using AG_2[of "x^2*y^2" "x^2*z^2"]
    using assms
    by (simp add: mult.assoc)
  then have "(x^2*y^2 + x^2*z^2) \<ge> 2*sqrt(x^2*y^2 * x^2*z^2)"
    by simp
  then have "(x^2*y^2 + x^2*z^2) \<ge> 2*sqrt(x^4*y^2*z^2)"
    by (smt mult.assoc mult.commute numeral_Bit0 power_add)
  then have "x^2*y^2 + x^2*z^2 \<ge> 2* (root 2 (x^4*y^2*z^2))"
    by (simp add: sqrt_def)
  then have "x^2*y^2 + x^2*z^2 \<ge> 2* (x^2*y*z)"
    by (smt assms(2) assms(3) numeral_Bit0 power2_eq_square power_add real_root_mult real_sqrt_abs sqrt_def zero_le_power2)
  then show ?thesis
    by simp
qed

(* Iz ove nejednakosti izvlačimo ključnu nejednakost k3, ali svakako moramo da pokažemo
   da i ona važi *)
lemma nejednakost_3_1 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> x^2*y*z + x*y^2*z + x*y*z^2"
proof-
  have 1: "y^2*x^2 + y^2*z^2 \<ge> 2*y^2*x*z"
    using assms
    by simp

  have 2: "x^2*y^2  + x^2*z^2 \<ge> 2*x^2*y*z"
    using assms
    by simp

  have 3: "z^2*y^2 + z^2*x^2 \<ge> 2*z^2*y*x"
    using assms
    by simp

  have "y^2*x^2 + y^2*z^2 + x^2*y^2  + x^2*z^2 + z^2*y^2 + z^2*x^2 \<ge>  2*y^2*x*z +  2*x^2*y*z + 2*z^2*y*x"
    using 1 2 3 assms
    by linarith
  then have "2*(y^2*x^2 + y^2*z^2 + x^2*z^2) \<ge> 2 * (y^2*x*z + x^2*y*z + z^2*y*x)"
    using assms
    by (simp add: mult.commute)
  then show ?thesis
    by (simp add: mult.commute)
qed

(* Jedna od ključnih nejednakosti koju ćemo primeniti u lemi kk *)
lemma k3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> x^2*y*z + x*y^2*z + x*y*z^2"
  shows "(x*y*z*(x + y + z))/((x*y + y*z + z*x)^2) \<le> 1/3"
proof-

  from assms(4)
  have "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> x*y*z * (x + y + z)"
    by (simp add: \<open>x\<^sup>2 * y * z + x * y\<^sup>2 * z + x * y * z\<^sup>2 \<le> x\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2 + z\<^sup>2 * x\<^sup>2\<close> add.assoc add.commute add.left_commute add_diff_eq diff_add_eq diff_diff_add diff_diff_eq2 distrib_left mult.commute mult.left_commute power_mult_distrib right_diff_distrib' power2_eq_square)
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> (3-2) * (x*y*z * (x + y + z))"
    by simp
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 \<ge> 3*x*y*z * (x + y + z) - 2*x*y*z * (x + y + z) "
    by simp
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 + 2*x*y*z * (x + y + z) \<ge> 3*x*y*z * (x + y + z)"
    by simp
  then have "x^2*y^2 + y^2*z^2 + z^2*x^2 + 2*x^2*y*z + 2*x*y^2*z + 2*x*y*z^2 \<ge> 3*x*y*z * (x + y + z)"
    by (simp add: distrib_right mult.commute power2_eq_square)
  then have * : "(x*y + y*z + z*x)^2 \<ge> 3*x*y*z * (x + y + z)"
    by (simp add: add.left_commute distrib_left left_diff_distrib mult.commute mult.left_commute right_diff_distrib power2_eq_square)

  have "(x*y + y*z + z*x)^2 \<ge> 3*x*y*z * (x + y + z)"
    using assms(1) assms(2) assms(3)  
    using *
    by simp
  then have ** : "1/(x*y + y*z + z*x)^2 \<le> 1/(3*x*y*z * (x + y + z))"
    using assms(1) assms(2) assms(3)
    by (smt frac_le mult_pos_pos)

  have "(x*y*z*(x + y + z))/((x*y + y*z + z*x)^2) \<le> x*y*z*(x + y + z) * (1/(x*y + y*z + z*x)^2)"
    by simp
  also have "... \<le> x*y*z*(x + y + z) * (1/(3*x*y*z * (x + y + z)))"
    using **
    by (meson add_nonneg_nonneg assms(1) assms(2) assms(3) less_imp_le mult_left_mono mult_nonneg_nonneg)
  also have "... \<le> x*y*z*(x + y + z)/(3*x*y*z * (x + y + z))"
    by simp
  also have "... \<le> 1/3"
    using assms(1) assms(2) assms(3)
    by simp
  finally show ?thesis
    .
qed

(* Nejednakost koja će biti primenjena na izraz u glavnoj lemi 
            (kombinacija svih ključnih nejednakosti)           *)
lemma kk:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  assumes "1/x + 1/y + 1/z = x + y + z"
  shows "(((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x))) * ((x*y + y*z + z*x)/(x*y*z*(x + y + z))) * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2)) \<le> 3/8"
proof-

  have 11 : "((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 1 : "((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x)) \<le> 9/8"
    using assms(1) assms(2) assms(3)
    using k1
    by simp

  have 22 : "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 2 : "(x*y + y*z + z*x)/(x*y*z*(x + y + z)) \<le> 1"
    using assms(1) assms(2) assms(3) assms(4)
    using k2
    by simp

  have 33 : "((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff zero_less_power)

  have 3 : "((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2)) \<le> 1/3"
    using assms(1) assms(2) assms(3)
    using k3
    by simp

  have " (((x + y + z)*(x*y + y*z + z*x))/((x + y)*(y + z)*(z + x))) * ((x*y + y*z + z*x)/(x*y*z*(x + y + z))) * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2))
       \<le> 9/8 * ((x*y + y*z + z*x)/(x*y*z*(x + y + z))) * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2))"
    using 1 11 22 33
    using assms(1) assms(2) assms(3)
    using real_mult_le_cancel_iff1 
    by blast
  also have " ...  \<le> 9/8 * 1 * ((x*y*z*(x + y + z))/((x*y + y*z + z*x)^2))"
    using 2 11 22 33
    using assms(1) assms(2) assms(3)
    by (metis divide_nonneg_nonneg mult_left_mono real_mult_le_cancel_iff1 zero_le_numeral)
  also have " ... \<le> 9/8 * 1 * 1/3"
    using 3 11 22 33
    using assms(1) assms(2) assms(3)
    by simp
  finally show ?thesis
    by simp
qed

(* Pomoćna lema *)
lemma pomocna:
  fixes x :: real
  assumes "x > 0" "x \<le> 3/8"
  shows "1/2 * x \<le> 1/2 * 3/8"
  using assms
  by simp

(* Glavna lema *)
lemma glavna :
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" 
  assumes "1/a + 1/b + 1/c = a + b + c"
  shows " (1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 3/16"
proof-
  
  have 1 : "1/((2*a + b + c)^2) \<le> 1/(4*(a + b)*(a + c))"
    using assms(1) assms(2) assms(3)
    using nejednakost
    by simp

  have 2 : "1/((2*b + c + a)^2) \<le> 1/(4*(b + c)*(b + a))"
    using assms(1) assms(2) assms(3)
    using nejednakost
    by simp

  have 3 : "1/((2*c + a + b)^2) \<le> 1/(4*(c + a)*(c + b))"
    using assms(1) assms(2) assms(3)
    using nejednakost
    by simp


  have "(1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 
      1/(4*(a + b)*(a + c)) + 1/(4*(b + c)*(b + a)) + 1/(4*(c + a)*(c + b))"
    using 1 2 3
    by simp
  also have " ... = (b + c)/(4*(a + b)*(a + c)*(b + c)) + (a + c)/(4*(b + c)*(b + a)*(a + c)) + (a + b)/(4*(c + a)*(c + b)*(a + b))"
    using assms(1) assms(2) assms(3)
    by simp
  also have "... = (b + c + c + a + a + b)/(4*(a + b)*(b + c)*(c + a))"
    using assms(1) assms(2) assms(3)
    by (metis (mono_tags, hide_lams) add.commute add.left_commute add_divide_distrib mult.commute mult.left_commute)
  also have "... = (2*(a + b + c))/(4*(a + b)*(b + c)*(c + a))"
    by simp
  also have "... = (2/4)*((a + b + c)/((a + b)*(b + c)*(c + a)))"
    proof -
      have "\<forall>r ra rb. (ra::real) * (rb / r) = rb * ra / r"
        by auto
      then show ?thesis
        by (metis (no_types) divide_divide_eq_left)
    qed
  also have "... = (1/2)*((a + b + c)/((a + b)*(b + c)*(c + a)))"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a))"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * 1"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * (a*b*c) / (a*b*c) "
    using assms(1) assms(2) assms(3)
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * (a*b*c) / (a*b*c) * (a + b + c) / (a + b + c)"
    by simp
  also have "... = (a + b + c)/(2*(a + b)*(b + c)*(c + a)) * (a*b*c) / (a*b*c) * (a + b + c) / (a + b + c) * ((a*b + b*c + c*a)^2) / ((a*b + b*c + c*a)^2) "
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos nonzero_mult_div_cancel_right zero_less_power)
  also have "... = (((a + b + c)*(a*b + b*c + c*a))/(2*(a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    by (simp add: power2_eq_square)
  also have  "... = 1/2*(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    by simp
  finally have pocetak : "(1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 
        1/2*(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a+b+c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    by simp


  have 11 : "((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 22 : "(a*b + b*c + c*a)/(a*b*c*(a + b + c)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff)

  have 33 : "((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) > 0"
    using assms(1) assms(2) assms(3)
    by (smt mult_pos_pos zero_less_divide_iff zero_less_power)


  have * : "(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a+b+c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) > 0"
    using assms(1) assms(2) assms(3)
    using 11 22 33
    using zero_less_mult_iff 
    by blast
     
  have ** : "(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) \<le> 3/8"
    using assms(1) assms(2) assms(3) assms(4)
    using kk
    by simp

    
  have kraj : "1/2* (((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2)) \<le>
        1/2 * 3/8"
    using *
    using **
    using pomocna[of "(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"]
    by auto

  have "(1/(2*a + b + c)^2) + (1/(2*b + c + a)^2) + (1/(2*c + a + b)^2) \<le> 
          1/2*(((a + b + c)*(a*b + b*c + c*a))/((a + b)*(b + c)*(c + a))) * ((a*b + b*c + c*a)/(a*b*c*(a + b + c))) * ((a*b*c*(a + b + c))/((a*b + b*c + c*a)^2))"
    using pocetak
    by simp
  also have "... \<le> 1/2 * 3/8"
    using kraj
    by simp
  finally show ?thesis
    by simp
qed


end