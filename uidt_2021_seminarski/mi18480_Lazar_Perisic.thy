theory mi18480_Lazar_Perisic
  imports Complex_Main
begin


(* ----------------------------------------- *)

(* Pomocne leme *)

(* Šurova nejednakost *)

(* Ako su a, b, c pozitivni realni brojevi i n je realan broj ,tada je 
   a^n * (a – b) * (a – c) + b^n * (b – c) * (b – a) + c^n * (c – a) * ( c – b) \<ge> 0
   sa jednakoscu ako i samo ako je a = b = c. *)

(* n=1 *)

lemma schurN1Unfolded:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)
        = a^3+b^3+c^3+3*a*b*c-a^2*c-b^2*a-c^2*b-a^2*b-b^2*c-c^2*a" (is "?L=?D")
proof -
  have "?L=(a^2-a*b)*(a-c)+(b^2-b*c)*(b-a)+(c^2-c*a)*(c-b)"
    by (simp add: power2_eq_square right_diff_distrib')
  also have "\<dots>=(a^2)*(a-c)-(a*b)*(a-c)+(b^2)*(b-a)-(b*c)*(b-a)+(c^2)*(c-b)-(c*a)*(c-b)"
    by (simp add: left_diff_distrib')
  also have "\<dots>=(a^3-a^2*c)-(a^2*b-a*b*c)+(b^3-b^2*a)-(b^2*c-a*b*c)+(c^3-c^2*b)-(c^2*a-a*b*c)"
    by (smt (verit, ccfv_threshold) add.commute add.right_neutral add_diff_eq calculation diff_add_cancel diff_add_eq diff_add_eq_diff_diff_swap diff_diff_add diff_diff_eq2 is_num_normalize(1) left_diff_distrib mult.commute mult.left_commute mult_zero_left mult_zero_right power2_eq_square power3_eq_cube right_diff_distrib)
  also have "\<dots>=(a^3-a^2*c-a^2*b+a*b*c)+(b^3-b^2*a-b^2*c+a*b*c)+(c^3-c^2*b-c^2*a+a*b*c)"
    by fastforce
  also have "\<dots>=?D"
    by simp
  finally show "?thesis"
    .
qed


(* ako su dva jednaka onda nejednakost vazi *)

lemma schur2EqualN1:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "(a=b \<and> b\<noteq>c) \<or> (a\<noteq>b \<and> b=c) \<or> (a=c \<and> b\<noteq>c)" 
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b) \<ge>0" (is "?L\<ge>0")
  by (smt (verit, best) assms(1) assms(2) assms(3) assms(4) mult_nonneg_nonpos zero_le_mult_iff)



(* ako su a, b i c jednaki onda je jednakost *)

lemma schur3EqualN1:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a=b" "b=c"
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b) =0" (is "?L=0")
  by (simp add: assms(4) assms(5))



(* dokazivanje sa > u also have *)

lemma schurN1V1:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  assumes "a > b" "b > c"
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
proof -
 have "?L=(a-b) *a  * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)"
    by simp
  also have "\<dots>=(a-b) *a  * (a-c) + b * (b-a) * (b-c) + c * (c-a) * (c-b)"
    by auto
  also have "\<dots>=(a-b) *a  * (a-c) + b * (-(a-b)) * (b-c) + c * (c-a) * (c-b)"
    by auto
  also have "\<dots>=(a-b) *a  * (a-c) - b * (a-b) * (b-c) + c * (c-a) * (c-b)"
    by linarith
  also have "\<dots>=(a-b) *(a  * (a-c) - b * (b-c)) + c * (c-a) * (c-b)"
    by (smt (verit) ab_semigroup_mult_class.mult_ac(1) mult.commute right_diff_distrib)
  also have "\<dots>=(a-b) *(a  * (a-c) - b * (b-c)) + c * (-(a-c)) * (-(b-c))"
    by simp
  also have "\<dots>=(a-b) *(a  * (a-c) - b * (b-c)) + c * (a-c) * (b-c)"
    by linarith
  also have "\<dots>>(a-b) *((a-b) * (b-c)) + c * (a-c) * (b-c)"
    by (simp add: assms(1) assms(7) mult_diff_mult)
  also have "\<dots>\<ge>0"
    by (smt (verit, best) \<open>(a - b) * ((a - b) * (b - c)) + c * (a - c) * (b - c) < (a - b) * (a * (a - c) - b * (b - c)) + c * (a - c) * (b - c)\<close> assms(3) assms(7) assms(8) mult_pos_pos)
  finally show "?L\<ge>0"
    by (smt (verit, ccfv_SIG) \<open>(a - b) * (a * (a - c) - b * (b - c)) + c * - (a - c) * - (b - c) = (a - b) * (a * (a - c) - b * (b - c)) + c * (a - c) * (b - c)\<close> \<open>(a - b) * a * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) = (a - b) * a * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b)\<close> \<open>(a - b) * a * (a - c) + b * - (a - b) * (b - c) + c * (c - a) * (c - b) = (a - b) * a * (a - c) - b * (a - b) * (b - c) + c * (c - a) * (c - b)\<close> \<open>(a - b) * a * (a - c) - b * (a - b) * (b - c) + c * (c - a) * (c - b) = (a - b) * (a * (a - c) - b * (b - c)) + c * (c - a) * (c - b)\<close> \<open>0 \<le> (a - b) * (a * (a - c) - b * (b - c)) + c * (a - c) * (b - c)\<close> \<open>a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) = (a - b) * a * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)\<close>)
qed



(* dokazivanje sa < u also have *)

lemma schurN1V2:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  assumes "a > b" "b > c"
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
proof -
  have "0\<le>(a-b) *((a-b) * (b-c)) + c * (a-c) * (b-c)"
    using assms(3) assms(7) assms(8) by auto
  also have "\<dots>=(a-b) *(a  *(b-c) - b * (b-c)) + c * (a-c) * (b-c)"
    by (simp add: left_diff_distrib)
  also have "\<dots><(a-b) *(a  * (a-c) - b * (b-c)) + c * (a-c) * (b-c)"
    by (simp add: assms(1) assms(7))
  also have "\<dots>=(a-b) *(a  * (a-c) - b * (b-c)) + c * (-(a-c)) * (-(b-c))"
    by linarith
  also have "\<dots>=(a-b) *(a  * (a-c) - b * (b-c)) + c * (c-a) * (c-b)"
    by simp
  also have "\<dots>=(a-b) *a  * (a-c) - b * (a-b) * (b-c) + c * (c-a) * (c-b)"
    by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) mult.left_commute right_diff_distrib)
  also have "\<dots>=(a-b) *a  * (a-c) + b * (-(a-b)) * (b-c) + c * (c-a) * (c-b)"
    by linarith
  also have "\<dots>=(a-b) *a  * (a-c) + b * (b-a) * (b-c) + c * (c-a) * (c-b)"
    by simp
  also have "\<dots>=(a-b) *a  * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)"
    by simp
  also have "\<dots>=a*(a-b)  * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)"
    by simp
  finally show ?thesis
    by simp  
qed
   
(* Sve permutacije a>b>c (a>c>b, b>a>c, b>c>a... *)

lemma schurN1V3:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a > b" "b > c" (*a>b>c*)
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
  using assms(3) assms(4) assms(5) schurN1V2 by force

lemma schurN1V4:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a > c" "c > b" (*a>c>b*)
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
  using assms schurN1V2[where a=a and b=c and c=b]
  by (smt (verit, del_insts) mult.assoc mult.commute)
 (* by (simp add: \<open>0 < a\<close> \<open>0 < b\<close> \<open>0 < c\<close> \<open>\<lbrakk>0 < a; 0 < c; 0 < b; a \<noteq> c; c \<noteq> b; b \<noteq> a; c < a; b < c\<rbrakk> \<Longrightarrow> 0 \<le> a * (a - c) * (a - b) + c * (c - b) * (c - a) + b * (b - a) * (b - c)\<close> \<open>b < a\<close> \<open>b < c\<close> \<open>c < a\<close> add.commute mult.commute mult.left_commute) *)

lemma schurN1V5:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "b > a" "a > c" (*b>a>c*)
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
  using assms(3) assms(4) assms(5) schurN1V4 by force

lemma schurN1V6:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "b > c" "c > a" (*b>c>a*)
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
  using assms(1) assms(4) assms(5) schurN1V3 by force

lemma schurN1V7:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "c > a" "a > b" (*c>a>b*)
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
  using assms(2) assms(4) assms(5) schurN1V6 by force

lemma schurN1V8:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a < b" "b < c" (*c>b>a*)
  shows "a * (a-b) * (a-c) + b * (b-c) * (b-a) + c * (c-a) * (c-b)\<ge>0" (is "?L\<ge>0")
  using assms(1) assms(4) assms(5) schurN1V4 by force
(*
  using assms schurN1V2[where a=a and b=c and c=b]
  using schurN1V4 by force
*)




(* ----------------------------------------- *)

(* Pomocne leme *)

lemma power5_eq_xxxxx: "x^5 = (x::real) * x * x * x * x" (is "?L=?D")
  by (smt (z3) mult.assoc power2_eq_square power3_eq_cube power4_eq_xxxx power_add_numeral semiring_norm(3))

lemma power6_eq_xxxxxx: "x^6 = (x::real) * x * x * x * x * x" (is "?L=?D")
  by (metis (no_types, lifting) mult.assoc numeral_Bit0 power3_eq_cube power_add)

lemma pomocna: "(a^3)*(b^6) = (a::real)*b^2*a*b^2*a*b^2" (is "?L=?D")
  by (simp add: power3_eq_cube)


(* ----------------------------------------- *)




(* Zadatak *)


text\<open>https://imomath.com/srb/zadaci/2015_bmo_resenja.pdf\<close>
text\<open>1\<close>
text\<open>Ako su a, b i c pozitivni brojevi, dokazati nejednakost
     (a^3)*(b^6)+(b^3)*(c^6)+(c^3)*(a^6)+3*(a^3)*(b^3)*(c^3)
     \<ge>a*b*c* ((a^3)*(b^3)+(b^3)*(c^3)+(c^3)*(a^3)) +(a^2)*(b^2)*(c^2)* ((a^3)+(b^3)+(c^3)\<close>

(* Svodimo zadatak na 
         (a^3)*(b^6)+(b^3)*(c^6)+(c^3)*(a^6)+3*(a^3)*(b^3)*(c^3)
         -(a*b*c* ((a^3)*(b^3)+(b^3)*(c^3)+(c^3)*(a^3)) +(a^2)*(b^2)*(c^2)* ((a^3)+(b^3)+(c^3)))\<ge>0 *)


lemma zadatak:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  shows "(a^3)*(b^6)+(b^3)*(c^6)+(c^3)*(a^6)+3*(a^3)*(b^3)*(c^3)
         -(a*b*c* ((a^3)*(b^3)+(b^3)*(c^3)+(c^3)*(a^3)) +(a^2)*(b^2)*(c^2)* ((a^3)+(b^3)+(c^3)))\<ge>0" (is "?L\<ge>0")
proof -
  let ?x="a*b^2"
  let ?y="b*c^2"
  let ?z="c*a^2"

 have "a*b^2>0"
    using assms(1) assms(2) by auto

  have "b*c^2>0"
    using assms(2) assms(3) by auto

  have "c*a^2>0"
    using assms(1) assms(3) by auto

  have "?L=(a^3)*(b^6)+(b^3)*(c^6)+(c^3)*(a^6)+3*(a^3)*(b^3)*(c^3)-(a*b*c*(a^3)*(b^3)+a*b*c*(b^3)*(c^3)+a*b*c*(c^3)*(a^3)+(a^2)*(b^2)*(c^2)* ((a^3)+(b^3)+(c^3)))"
    by (simp add: distrib_left)
  also have "\<dots>=(a^3)*(b^6)+(b^3)*(c^6)+(c^3)*(a^6)+3*(a^3)*(b^3)*(c^3)-(a*b*c*(a^3)*(b^3)+a*b*c*(b^3)*(c^3)+a*b*c*(c^3)*(a^3)+(a^2)*(b^2)*(c^2)*(a^3)+(a^2)*(b^2)*(c^2)*(b^3)+(a^2)*(b^2)*(c^2)*(c^3))"
    by (simp add: distrib_left)
  also have "\<dots>=(a^3)*(b^6)+(b^3)*(c^6)+(c^3)*(a^6)+3*(a^3)*(b^3)*(c^3)-(a^4*b^4*c+a*b^4*c^4+a^4*b*c^4+a^5*b^2*c^2+a^2*b^5*c^2+a^2*b^2*c^5)"
    by (simp add: mult.commute mult.left_commute power2_eq_square power3_eq_cube power4_eq_xxxx power5_eq_xxxxx)
  also have "\<dots>=a*b^2*a*b^2*a*b^2+b*c^2*b*c^2*b*c^2+c*a^2*c*a^2*c*a^2+3*a*b^2*b*c^2*c*a^2-(a^4*b^4*c+a*b^4*c^4+a^4*b*c^4+a^5*b^2*c^2+a^2*b^5*c^2+a^2*b^2*c^5)"
    by (simp add: mult.commute mult.left_commute power2_eq_square power3_eq_cube power6_eq_xxxxxx)
  also have "\<dots>=(a*b^2)^3+(b*c^2)^3+(c*a^2)^3+3*a*b^2*b*c^2*c*a^2-(a^4*b^4*c+a*b^4*c^4+a^4*b*c^4+a^5*b^2*c^2+a^2*b^5*c^2+a^2*b^2*c^5)"
    by (simp add: power3_eq_cube)
  also have "\<dots>=?x^3+?y^3+?z^3+3*?x*?y*?z-(?x^2*?z+?y^2*?x+?z^2*?y+?z^2*?x+?x^2*?y+?y^2*?z)"
    by (simp add: mult.commute mult.left_commute power2_eq_square power4_eq_xxxx power5_eq_xxxxx)
  also have *: "\<dots>=?x * (?x-?y) * (?x-?z) + ?y * (?y-?z) * (?y-?x) + ?z * (?z-?x) * (?z-?y)"
    unfolding schurN1Unfolded[where a="?x" and b="?y" and c="?z"]
    using \<open>\<lbrakk>0 < a * b\<^sup>2; 0 < b * c\<^sup>2; 0 < c * a\<^sup>2\<rbrakk> \<Longrightarrow> a * b\<^sup>2 * (a * b\<^sup>2 - b * c\<^sup>2) * (a * b\<^sup>2 - c * a\<^sup>2) + b * c\<^sup>2 * (b * c\<^sup>2 - c * a\<^sup>2) * (b * c\<^sup>2 - a * b\<^sup>2) + c * a\<^sup>2 * (c * a\<^sup>2 - a * b\<^sup>2) * (c * a\<^sup>2 - b * c\<^sup>2) = (a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * (a * b\<^sup>2) * (b * c\<^sup>2) * (c * a\<^sup>2) - (a * b\<^sup>2)\<^sup>2 * (c * a\<^sup>2) - (b * c\<^sup>2)\<^sup>2 * (a * b\<^sup>2) - (c * a\<^sup>2)\<^sup>2 * (b * c\<^sup>2) - (a * b\<^sup>2)\<^sup>2 * (b * c\<^sup>2) - (b * c\<^sup>2)\<^sup>2 * (c * a\<^sup>2) - (c * a\<^sup>2)\<^sup>2 * (a * b\<^sup>2)\<close> assms(1) assms(2) assms(3) by force
  also have "\<dots>\<ge>0"
    by (smt (verit) \<open>0 < a * b\<^sup>2\<close> \<open>0 < b * c\<^sup>2\<close> \<open>0 < c * a\<^sup>2\<close> schur2EqualN1 schur3EqualN1 schurN1V3 schurN1V4)
  finally show "?thesis"
    .

  
(* Drugi nacin

  have "?x * (?x-?y) * (?x-?z) + ?y * (?y-?z) * (?y-?x) + ?z * (?z-?x) * (?z-?y)\<ge>0"
     by (smt (verit) \<open>0 < a * b\<^sup>2\<close> \<open>0 < b * c\<^sup>2\<close> \<open>0 < c * a\<^sup>2\<close> schur2EqualN1 schur3EqualN1 schurN1V3 schurN1V4)
   finally show "?thesis"
    using "*" \<open>(a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5) = (a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * (a * b\<^sup>2) * (b * c\<^sup>2) * (c * a\<^sup>2) - ((a * b\<^sup>2)\<^sup>2 * (c * a\<^sup>2) + (b * c\<^sup>2)\<^sup>2 * (a * b\<^sup>2) + (c * a\<^sup>2)\<^sup>2 * (b * c\<^sup>2) + (c * a\<^sup>2)\<^sup>2 * (a * b\<^sup>2) + (a * b\<^sup>2)\<^sup>2 * (b * c\<^sup>2) + (b * c\<^sup>2)\<^sup>2 * (c * a\<^sup>2))\<close> \<open>0 \<le> a * b\<^sup>2 * (a * b\<^sup>2 - b * c\<^sup>2) * (a * b\<^sup>2 - c * a\<^sup>2) + b * c\<^sup>2 * (b * c\<^sup>2 - c * a\<^sup>2) * (b * c\<^sup>2 - a * b\<^sup>2) + c * a\<^sup>2 * (c * a\<^sup>2 - a * b\<^sup>2) * (c * a\<^sup>2 - b * c\<^sup>2)\<close> \<open>a * b\<^sup>2 * a * b\<^sup>2 * a * b\<^sup>2 + b * c\<^sup>2 * b * c\<^sup>2 * b * c\<^sup>2 + c * a\<^sup>2 * c * a\<^sup>2 * c * a\<^sup>2 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5) = (a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5)\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * (a ^ 3 + b ^ 3 + c ^ 3)) = a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * (a ^ 3 + b ^ 3 + c ^ 3))\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * (a ^ 3 + b ^ 3 + c ^ 3)) = a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * b ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * c ^ 3)\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * b ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * c ^ 3) = a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5)\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5) = a * b\<^sup>2 * a * b\<^sup>2 * a * b\<^sup>2 + b * c\<^sup>2 * b * c\<^sup>2 * b * c\<^sup>2 + c * a\<^sup>2 * c * a\<^sup>2 * c * a\<^sup>2 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5)\<close> by presburger
*)



(* Treci nacin
  have "?x * (?x-?y) * (?x-?z) + ?y * (?y-?z) * (?y-?x) + ?z * (?z-?x) * (?z-?y)\<ge>0"
    using * assms schurN1V2[where a="a*b^2" and b="b*c^2" and c="c*a^2"]
    using \<open>0 \<le> a * b\<^sup>2 * (a * b\<^sup>2 - b * c\<^sup>2) * (a * b\<^sup>2 - c * a\<^sup>2) + b * c\<^sup>2 * (b * c\<^sup>2 - c * a\<^sup>2) * (b * c\<^sup>2 - a * b\<^sup>2) + c * a\<^sup>2 * (c * a\<^sup>2 - a * b\<^sup>2) * (c * a\<^sup>2 - b * c\<^sup>2)\<close> by presburger
  finally show "?thesis"
    using "*" \<open>(a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5) = (a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * (a * b\<^sup>2) * (b * c\<^sup>2) * (c * a\<^sup>2) - ((a * b\<^sup>2)\<^sup>2 * (c * a\<^sup>2) + (b * c\<^sup>2)\<^sup>2 * (a * b\<^sup>2) + (c * a\<^sup>2)\<^sup>2 * (b * c\<^sup>2) + (c * a\<^sup>2)\<^sup>2 * (a * b\<^sup>2) + (a * b\<^sup>2)\<^sup>2 * (b * c\<^sup>2) + (b * c\<^sup>2)\<^sup>2 * (c * a\<^sup>2))\<close> \<open>0 \<le> a * b\<^sup>2 * (a * b\<^sup>2 - b * c\<^sup>2) * (a * b\<^sup>2 - c * a\<^sup>2) + b * c\<^sup>2 * (b * c\<^sup>2 - c * a\<^sup>2) * (b * c\<^sup>2 - a * b\<^sup>2) + c * a\<^sup>2 * (c * a\<^sup>2 - a * b\<^sup>2) * (c * a\<^sup>2 - b * c\<^sup>2)\<close> \<open>a * b\<^sup>2 * a * b\<^sup>2 * a * b\<^sup>2 + b * c\<^sup>2 * b * c\<^sup>2 * b * c\<^sup>2 + c * a\<^sup>2 * c * a\<^sup>2 * c * a\<^sup>2 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5) = (a * b\<^sup>2) ^ 3 + (b * c\<^sup>2) ^ 3 + (c * a\<^sup>2) ^ 3 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5)\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * (a ^ 3 + b ^ 3 + c ^ 3)) = a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * (a ^ 3 + b ^ 3 + c ^ 3))\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * (a ^ 3 + b ^ 3 + c ^ 3)) = a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * b ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * c ^ 3)\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c * a ^ 3 * b ^ 3 + a * b * c * b ^ 3 * c ^ 3 + a * b * c * c ^ 3 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * a ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * b ^ 3 + a\<^sup>2 * b\<^sup>2 * c\<^sup>2 * c ^ 3) = a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5)\<close> \<open>a ^ 3 * b ^ 6 + b ^ 3 * c ^ 6 + c ^ 3 * a ^ 6 + 3 * a ^ 3 * b ^ 3 * c ^ 3 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5) = a * b\<^sup>2 * a * b\<^sup>2 * a * b\<^sup>2 + b * c\<^sup>2 * b * c\<^sup>2 * b * c\<^sup>2 + c * a\<^sup>2 * c * a\<^sup>2 * c * a\<^sup>2 + 3 * a * b\<^sup>2 * b * c\<^sup>2 * c * a\<^sup>2 - (a ^ 4 * b ^ 4 * c + a * b ^ 4 * c ^ 4 + a ^ 4 * b * c ^ 4 + a ^ 5 * b\<^sup>2 * c\<^sup>2 + a\<^sup>2 * b ^ 5 * c\<^sup>2 + a\<^sup>2 * b\<^sup>2 * c ^ 5)\<close> by presburger
*)

qed






end