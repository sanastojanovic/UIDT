theory mi16100_Dara_Milojkovic
  imports Complex_Main
begin

text\<open>
https://imomath.com/srb/zadaci/BIH_2014_bihmo_resenja.pdf

Resavamo zadatak: Neka su a, b, c razliciti realni brojevi.
I) Izracunati vrednost izraza
  a) ((1+a*b) / (a-b)) * ((1+b*c)/(b-c)) + ((1+b*c) / (b-c)) * ((1+c*a)/(c-a)) + ((1+c*a) / (c-a)) * ((1+a*b)/(a-b))

  b) ((1-a*b) / (a-b)) * ((1-b*c)/(b-c)) + ((1-b*c) / (b-c)) * ((1-c*a)/(c-a)) + ((1-c*a) / (c-a)) * ((1-a*b)/(a-b))

II) Dokazati nejednakost 
  (1+a^2*b^2)/(a-b)^2 + (1+b^2*c^2)/(b-c)^2 +  (1+c^2*a^2)/(c-a)^2 \<ge> (3::real) / (2::real)
 Da li moze nastupiti znak jednakosti?
\<close>


(*Pravimo funkcije koje izracunavaju vrednost izraza sa nekim izabranim brojevima*)
fun racunanjeIzrazaA::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"racunanjeIzrazaA a b c = ((1+a*b) / (a-b)) * ((1+b*c)/(b-c)) + ((1+b*c) / (b-c)) * ((1+c*a)/(c-a)) + ((1+c*a) / (c-a)) * ((1+a*b)/(a-b))"

fun racunanjeIzrazaB::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"racunanjeIzrazaB a b c = ((1-a*b) / (a-b)) * ((1-b*c)/(b-c)) + ((1-b*c) / (b-c)) * ((1-c*a)/(c-a)) + ((1-c*a) / (c-a)) * ((1-a*b)/(a-b))"

(*Proveravamo koja je vrednost koji vracaju i dobijamo za razlicite brojeve 1 (-1) a za iste brojeve 0*)
value "racunanjeIzrazaA 1 2 3"

value "racunanjeIzrazaB 1 2 3"

(*sledece dve teoreme pokazuju da postoji neko a b c i ako je neki par isti funkcije vracaju 0 
jer Isabelle vraca 0*)
lemma [simp]:shows "\<exists> a b c::real. a=b \<or> a=c \<or> b=c \<longrightarrow> racunanjeIzrazaA a b c = 0"
  using numeral_eq_iff by blast

lemma shows "\<exists> a b c::real. a=b \<or> b=c \<or> a=c \<longrightarrow> racunanjeIzrazaB a b c = 0"
  by auto

(*sledece dve teoreme pokazuju da za svako a b c koji su medjusobno razliciti funkcije vracaju 1 odnosno -1*)
lemma shows "\<forall> a b c::real. a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<longrightarrow> racunanjeIzrazaA a b c = 1"
  sorry

lemma shows "\<forall> a b c::real. a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<longrightarrow> racunanjeIzrazaB a b c = (-1)"
  sorry
(*zadatak pod b). Postoje neki brojevi a b c za koje ce ova nejednakost biti tacna*)
lemma 
  fixes a b c::real
  assumes "a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
  shows " (1+a\<^sup>2*b\<^sup>2)/(a-b)\<^sup>2 + (1+b\<^sup>2*c\<^sup>2)/(b-c)\<^sup>2 +  (1+c\<^sup>2*a\<^sup>2)/(c-a)\<^sup>2 \<ge> (3::real) / (2::real)"
  using assms 
  sorry

(*postavlja se pitanje da li se moze umesto znaka \<ge> staviti znak jednakosti? Isabelle je mogao ovo da dokaze te je odgovor da.*)
lemma 
  shows "\<exists> a b c::real. a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<longrightarrow> (1+a\<^sup>2*b\<^sup>2)/(a-b)\<^sup>2 + (1+b\<^sup>2*c\<^sup>2)/(b-c)\<^sup>2 +  (1+c\<^sup>2*a\<^sup>2)/(c-a)\<^sup>2 =(3::real) / (2::real)"
  by blast


text\<open>
Drugi seminarski: dokazati sledece teoreme/leme. 
1. Definisemo koren kompleksnog broja
2. Dokazati da kvadrirani koren kompleksnog broja taj isti kompleksan broj
3. Pokazujemo da postoji neki kompleksan broj s koji pomnozen samim sobom daje neki drugi kompleksan broj z 
4. Iz prethodne leme pokazujemo da je taj kompleksan broj s bas koren broja z
5. Koren proizvoda dva kompleksna broja je proizvod korena dva kompleksna broja
6. Pravi se paralela izmedju kvadratne jednacine realnih brojeva i kvadratne jednacine kompleksnih brojeva
\<close>

definition "ccsqrt z = rcis (sqrt (cmod z)) (arg z / 2)"

(*ideja se oslanja na osobinu da su dva kompleksna broja jednaka ako su 
im jednaki realni deo i imaginarni deo*)
lemma square_ccsqrt [simp]:
  shows "(ccsqrt x)\<^sup>2 = x"
proof
  show "Re ((ccsqrt x)\<^sup>2) = Re x"
  proof-
    have "Re ((ccsqrt x)\<^sup>2) = Re (ccsqrt x * ccsqrt x)"
      by (simp add: power2_eq_square)
    also have "... = Re ((rcis (sqrt (cmod x)) (arg x / 2)) * (rcis (sqrt (cmod x)) (arg x / 2)))"
      using ccsqrt_def by presburger
    also have "... = Re (rcis (sqrt (cmod x) * sqrt (cmod x)) (arg x / 2 + arg x / 2))"
      using rcis_mult by presburger
    also have "... = Re (rcis (cmod x) (arg x))"
      by (metis abs_norm_cancel field_sum_of_halves real_sqrt_mult_self)
    also have "... = Re x"
      using rcis_cmod_arg by presburger
    finally show ?thesis .
  qed
next
  show "Im ((ccsqrt x)\<^sup>2) = Im x"
  proof-
    have "Im ((ccsqrt x)\<^sup>2) = Im (ccsqrt x * ccsqrt x)"
      by (simp add: power2_eq_square)
    also have "... = Im ((rcis (sqrt (cmod x)) (arg x / 2)) * (rcis (sqrt (cmod x)) (arg x / 2)))"
      using ccsqrt_def by presburger
    also have "... = Im (rcis (sqrt (cmod x) * sqrt (cmod x)) (arg x / 2 + arg x / 2))"
      using rcis_mult by presburger
    also have "... = Im (rcis (cmod x) (arg x))"
      by (metis abs_norm_cancel field_sum_of_halves real_sqrt_mult_self)
    also have "... = Im x"
      using rcis_cmod_arg by presburger
    finally show ?thesis .
  qed
qed
(*ista ideja se primenjuje i ovde*)
lemma ex_complex_sqrt [simp]:
  shows "\<exists> s::complex. s*s = z"
  apply (rule_tac x = "ccsqrt z" in exI)
proof 
  show "Re (ccsqrt z * ccsqrt z) = Re z"
  proof-
    have "Re (ccsqrt z * ccsqrt z) = Re ((rcis (sqrt (cmod z)) (arg z / 2)) * (rcis (sqrt (cmod z)) (arg z / 2)))"
      using ccsqrt_def by presburger
    also have "... = Re (rcis (sqrt (cmod z) * sqrt (cmod z)) (arg z /2 + arg z / 2))"
      using rcis_mult by presburger
    also have "... = Re (rcis (cmod z) (arg z))"
    by (metis ccsqrt_def power2_eq_square rcis_cmod_arg rcis_mult square_ccsqrt)
  also have "... = Re z"
    using rcis_cmod_arg by presburger
  finally show ?thesis .
  qed
next
  show "Im (ccsqrt z * ccsqrt z) = Im z"
  proof-
    have "Im (ccsqrt z * ccsqrt z) = Im ((rcis (sqrt (cmod z)) (arg z / 2)) * (rcis (sqrt (cmod z)) (arg z / 2)))"
      using ccsqrt_def by presburger
    also have "... = Im (rcis (sqrt (cmod z) * sqrt (cmod z)) (arg z /2 + arg z / 2))"
      using rcis_mult by presburger
    also have "... = Im (rcis (cmod z) (arg z))"
    by (metis ccsqrt_def power2_eq_square rcis_cmod_arg rcis_mult square_ccsqrt)
  also have "... = Im z"
    using rcis_cmod_arg by presburger
  finally show ?thesis .
  qed
qed


lemma ccsqrt [simp]:
  assumes "s*s = z"
  shows "s = ccsqrt z \<or> s = -ccsqrt z"
proof-
  have "s\<^sup>2 = s*s"
    by (simp add: power2_eq_square)
  then have "... = z"
    using assms
    by simp
  then have "... = ccsqrt z * ccsqrt z"
    by (metis power2_eq_square square_ccsqrt)
  then have "... = (ccsqrt z)\<^sup>2"
    by auto
  then have "s\<^sup>2 = (ccsqrt z)\<^sup>2"
    using \<open>s\<^sup>2 = s * s\<close> assms by auto
  then have "s = ccsqrt z \<or> s = -ccsqrt z"
    using power2_eq_iff by blast
  then show ?thesis.
qed


lemma ccsqrt_mult [simp]:
  shows  "ccsqrt (a*b) = ccsqrt a * ccsqrt b \<or> ccsqrt (a*b) = - ccsqrt a * ccsqrt b"
proof - 
  have "(ccsqrt (a*b))^2 = a*b"
  by simp
  then have "a * b = (ccsqrt a * ccsqrt a) * (ccsqrt b * ccsqrt b)"
    by (metis power2_eq_square square_ccsqrt)
  then have "... = (ccsqrt a * ccsqrt b)*(ccsqrt a * ccsqrt b)"
    by simp
  then have "... = (ccsqrt a * ccsqrt b)^2"
    by (simp add: semiring_normalization_rules(29))
  then have "(ccsqrt (a*b))\<^sup>2 = (ccsqrt a * ccsqrt b)\<^sup>2"
  by (simp add: \<open>a * b = ccsqrt a * ccsqrt a * (ccsqrt b * ccsqrt b)\<close> \<open>ccsqrt a * ccsqrt a * (ccsqrt b * ccsqrt b) = ccsqrt a * ccsqrt b * (ccsqrt a * ccsqrt b)\<close>)
  then have "ccsqrt (a*b) = ccsqrt a * ccsqrt b \<or> ccsqrt (a*b) = - ccsqrt a * ccsqrt b"
    using power2_eq_iff by fastforce
  then show ?thesis.
qed

(*neke pomocne leme za resavanje izraza*)
lemma pomocna [simp]:
  fixes a b :: complex
  shows "(a/b)\<^sup>2 = a\<^sup>2 / b\<^sup>2"
  by (simp add: power_divide)

lemma pomocna1 [simp]:
  fixes a b ::complex
  shows "(a - b)\<^sup>2 = a\<^sup>2 - 2*a*b + b\<^sup>2"
  by (simp add: power2_diff)

lemma pomocna2 [simp]:
  fixes a b::complex
  shows "(a*b\<^sup>2)/(4*a\<^sup>2) = b\<^sup>2 / (4*a) "
  by (simp add: power2_eq_square)

lemma pomocna3 [simp]:
  fixes a b c::complex
  shows "(a*2*b*c) / (4*a\<^sup>2) = (b*c) / (2*a)"
proof-
  have "(a*2*b*c) / (4*a\<^sup>2) = (2*a*b*c) / (4*a\<^sup>2)"
    by auto
  also have "... = (2*a)*(b*c) / (2*a)\<^sup>2"
    by auto
  finally show ?thesis
    by (simp add: power2_eq_square)
qed

lemma pomocna4 [simp]:
  fixes a b::complex
  assumes "a\<noteq>0"
  shows " - (4*a*b) / (4*a) = -b"
  using assms by auto

lemma pomocna5 [simp]:
  fixes a b:: complex
  shows "(-a+b)\<^sup>2 = a\<^sup>2 - 2*a*b + b\<^sup>2"
  by auto

lemma pomocna6 [simp]:
  fixes a b::complex
  shows "(-a-b)\<^sup>2 = a\<^sup>2 + 2*a*b + b\<^sup>2"
  by simp

(*dodala sam pretpostavku da je a razlicito od nule kako bi moglo da se deli sa a*)
lemma quadratic_equation_complex:
  fixes a b c x :: complex
  assumes "a \<noteq> 0"
  shows "a*x\<^sup>2+b*x+c=0 \<longleftrightarrow> x = (-b + ccsqrt (b\<^sup>2-4*a*c)) / (2*a) \<or> x = (-b - ccsqrt (b\<^sup>2 - 4*a*c)) / (2*a)"
proof
  assume "x = (- b + ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> x = (- b - ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)"
  show "a*x\<^sup>2 + b*x+c=0"
  proof-
    have "a*x\<^sup>2 + b*x+c=a* ((- b + ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a))\<^sup>2 + b * ((- b + ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) + c   \<or> a*x\<^sup>2 + b*x+c= a* ((- b - ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a))\<^sup>2 + b * ((- b - ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) + c "
      using \<open>x = (- b + ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> x = (- b - ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> by blast
    then have "a*x\<^sup>2 + b*x+c = a * ((- b + ccsqrt (b\<^sup>2 - 4 * a * c))\<^sup>2 / (2*a)\<^sup>2) +  b * ((- b + ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) + c \<or> a*x\<^sup>2 + b*x+c = a* ((- b - ccsqrt (b\<^sup>2 - 4 * a * c))\<^sup>2 / (2 * a)\<^sup>2) + b * ((- b - ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) + c "
      by simp
    then have "a*x\<^sup>2 + b*x+c = a * ((- b + ccsqrt (b\<^sup>2 - 4 * a * c))\<^sup>2 / (2*a)\<^sup>2) +  (b*(- b + ccsqrt (b\<^sup>2 - 4 * a * c))) / (2 * a) + c \<or> a*x\<^sup>2 + b*x+c=a * ((- b - ccsqrt (b\<^sup>2 - 4 * a * c))\<^sup>2 / (2*a)\<^sup>2) +  (b*(- b - ccsqrt (b\<^sup>2 - 4 * a * c))) / (2 * a) + c "
      by simp
    then have "a*x\<^sup>2 + b*x+c = a * ((b\<^sup>2-2*b*(ccsqrt (b\<^sup>2 - 4 * a * c)) + (ccsqrt (b\<^sup>2 - 4 * a * c))\<^sup>2) / (4*a\<^sup>2)) +  (b*(- b + ccsqrt (b\<^sup>2 - 4 * a * c))) / (2 * a) + c \<or> a*x\<^sup>2 + b*x+c=a * ((b\<^sup>2 + 2*b*(ccsqrt (b\<^sup>2 - 4 * a * c)) + (ccsqrt (b\<^sup>2 - 4 * a * c))\<^sup>2)/(4*a\<^sup>2)) +  (b*(- b - ccsqrt (b\<^sup>2 - 4 * a * c))) / (2 * a) + c "
      by auto
    then have "a*x\<^sup>2 + b*x+c = a * ((b\<^sup>2-2*b*(ccsqrt (b\<^sup>2 - 4 * a * c)) + (b\<^sup>2 - 4 * a * c)) / (4*a\<^sup>2)) +  (-b\<^sup>2 + b*ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) + c \<or> a*x\<^sup>2 + b*x+c=a * ((b\<^sup>2 + 2*b*(ccsqrt (b\<^sup>2 - 4 * a * c)) + (b\<^sup>2 - 4 * a * c))/(4*a\<^sup>2)) +  (- b\<^sup>2 - b*ccsqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) + c "
      by (smt diff_0 mult_zero_right power2_eq_square right_diff_distrib square_ccsqrt uminus_add_conv_diff)
    then have "a*x\<^sup>2 + b*x+c = ((b\<^sup>2-2*b*(ccsqrt (b\<^sup>2 - 4 * a * c)) + (b\<^sup>2 - 4 * a * c)) / (4*a)) -b\<^sup>2/(2*a) + b*ccsqrt (b\<^sup>2 - 4 * a * c) / (2 * a) + c \<or> a*x\<^sup>2 + b*x+c=((b\<^sup>2 + 2*b*(ccsqrt (b\<^sup>2 - 4 * a * c)) + (b\<^sup>2 - 4 * a * c))/(4*a)) - b\<^sup>2/(2*a) - b*ccsqrt (b\<^sup>2 - 4 * a * c) / (2 * a) + c"
    by (smt ab_group_add_class.ab_diff_conv_add_uminus add.assoc add_divide_distrib minus_divide_left pomocna2 pomocna5 pomocna6 square_ccsqrt times_divide_eq_right)
  then have "a*x\<^sup>2 + b*x+c = b\<^sup>2 / (4*a)-2*b*(ccsqrt (b\<^sup>2 - 4 * a * c))/(4*a) + b\<^sup>2/(4*a) - (4 * a * c) / (4*a) -b\<^sup>2/(2*a) + b*ccsqrt (b\<^sup>2 - 4 * a * c) / (2 * a) + c \<or> a*x\<^sup>2 + b*x+c=b\<^sup>2/(4*a) + 2*b*(ccsqrt (b\<^sup>2 - 4 * a * c))/(4*a) + b\<^sup>2/(4*a) - (4 * a * c)/(4*a) - b\<^sup>2/(2*a) - b*ccsqrt (b\<^sup>2 - 4 * a * c) / (2 * a) + c"
    by (simp add: add_divide_distrib diff_divide_distrib)
  then have  "a*x\<^sup>2 + b*x+c = b\<^sup>2 / (4*a)-b*(ccsqrt (b\<^sup>2 - 4 * a * c))/(2*a) + b\<^sup>2/(4*a) - c -b\<^sup>2/(2*a) + b*ccsqrt (b\<^sup>2 - 4 * a * c) / (2 * a) + c \<or> a*x\<^sup>2 + b*x+c=b\<^sup>2/(4*a) + b*(ccsqrt (b\<^sup>2 - 4 * a * c))/(2*a) + b\<^sup>2/(4*a) - c - b\<^sup>2/(2*a) - b*ccsqrt (b\<^sup>2 - 4 * a * c) / (2 * a) + c"
    using assms by auto
  then have "a*x\<^sup>2 + b*x+c = b\<^sup>2 / (4*a) + b\<^sup>2/(4*a)  -b\<^sup>2/(2*a)  \<or> a*x\<^sup>2 + b*x+c=b\<^sup>2/(4*a)  + b\<^sup>2/(4*a) - b\<^sup>2/(2*a)"
    by simp
  then have "a*x\<^sup>2 + b*x+c = 2*b\<^sup>2 / (4*a)   -b\<^sup>2/(2*a)  \<or> a*x\<^sup>2 + b*x+c=2*b\<^sup>2/(4*a) - b\<^sup>2/(2*a)"
    by auto
  then have "a*x\<^sup>2 + b*x+c = b\<^sup>2 / (2*a)   -b\<^sup>2/(2*a)  \<or> a*x\<^sup>2 + b*x+c=b\<^sup>2/(2*a) - b\<^sup>2/(2*a)"
    by auto
  then have "a*x\<^sup>2 + b*x+c = 0  \<or> a*x\<^sup>2 + b*x+c=0"
    by simp
  then show ?thesis 
    by blast
qed
next 
  assume "a * x\<^sup>2 + b * x + c = 0 "
  show "x = (- b + ccsqrt (b\<^sup>2 - 4 * a * c)) / (2*a) \<or> x = (- b - ccsqrt (b\<^sup>2 - 4 * a * c)) / (2*a)"
  proof-
    have "a*x\<^sup>2+b*x+c = 0 \<longleftrightarrow> 4*a*(a*x\<^sup>2+b*x+c) = 0"
      by (simp add: \<open>a * x\<^sup>2 + b * x + c = 0\<close>)
    also have "4*a*(a*x\<^sup>2+b*x+c) = 4*a\<^sup>2*x\<^sup>2 +4*a*b*x + 4*a*c + b\<^sup>2 -b\<^sup>2"
      by (simp add: distrib_left power2_eq_square)
    also have "... = (2*a*x+b)\<^sup>2 -b\<^sup>2+4*a*c"
    by (smt add_diff_cancel_right' mult_2_right numeral_Bit0 power2_eq_square power2_sum semiring_normalization_rules(16) semiring_normalization_rules(18) semiring_normalization_rules(23))
  also have "(2*a*x+b)\<^sup>2 - b\<^sup>2 + 4*a*c=0"
    using \<open>a * x\<^sup>2 + b * x + c = 0\<close> calculation by blast
  also have "(2*a*x+b)\<^sup>2 = b\<^sup>2 - 4*a*c"
    by (metis \<open>(2 * a * x + b)\<^sup>2 - b\<^sup>2 + 4 * a * c = 0\<close> add_diff_cancel diff_0 diff_add_cancel uminus_add_conv_diff)
  then have "2*a*x+b = ccsqrt (b\<^sup>2 - 4*a*c) \<or> 2*a*x + b = -ccsqrt (b\<^sup>2 - 4*a*c)"
    by (metis \<open>(2 * a * x + b)\<^sup>2 = b\<^sup>2 - 4 * a * c\<close> ccsqrt power2_eq_square)
  then have "2*a*x = -b + ccsqrt (b\<^sup>2 - 4*a*c) \<or> 2*a*x = -b-ccsqrt (b\<^sup>2 - 4*a*c)"
    by (smt \<open>2 * a * x + b = ccsqrt (b\<^sup>2 - 4 * a * c) \<or> 2 * a * x + b = - ccsqrt (b\<^sup>2 - 4 * a * c)\<close> diff_minus_eq_add eq_diff_eq uminus_add_conv_diff)
  then have "x = (-b+ccsqrt (b\<^sup>2 - 4*a*c)) / (2*a) \<or> x = (-b - ccsqrt (b\<^sup>2 - 4*a*c))/ (2*a)"
    by (metis assms divisors_zero nonzero_mult_div_cancel_left zero_neq_numeral)
  thus ?thesis .
  qed
qed




end
