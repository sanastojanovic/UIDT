theory mi16091_Kristina_Pantelic
imports Main Complex_Main 
begin

text \<open>
  Sa linka https://imomath.com/srb/zadaci/BIH_2004_bihmo_resenja.pdf
  odabran je zadatak 3. prvog dana takmicenja.

  Neka su a, b, realni, pozitivni brojevi i a*b*c=1. Dokazati nejednakost
  a*b / (a^5 + b^5 + a*b) + b*c / (b^5 + c^5 + b*c) + a*c / (c^5 + a^5 + a*c) \<le> 1
 
  Drugi deo seminarskog je raspisivanje dokaza prvog seminarskog.
\<close>

fun glavni_izraz::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"glavni_izraz a b c = a*b / (a^5 + b^5 + a*b) + b*c / (b^5 + c^5 + b*c) + a*c / (c^5 + a^5 + a*c)"

value "glavni_izraz 1 1 1"
value "glavni_izraz 1 2 2"

(*
fun sabiranje:: "real\<Rightarrow>real\<Rightarrow>real" (infixl "\<oplus>" 100) where
"a \<oplus> b = a + b"

value "(3 - 2)::real"
*)

lemma pomocna1[simp]:
  assumes "\<forall> a b c :: real. a > 0 \<and> b > 0 \<and> c > 0 \<and> a * b * c = 1"
  shows "(a^3 - b^3) * (a^2 - b^2) \<ge> 0"
 (* using assms
  by blast*)
proof-
  fix a b c ::real
  have "(a^3 - b^3) * (a^2 - b^2) = (a - b)*(a^2 + ab + b^2)*(a - b)*(a+b)"
    using assms (*koristi se osobina komutativnost mnozenja*)
    by blast
  then have "(a - b)*(a^2 + ab + b^2)*(a - b)*(a+b) = (a-b)*(a-b)*(a^2 + ab + b^2)*(a+b)"
    by auto
  then have "(a-b)*(a-b)*(a^2 + ab + b^2)*(a+b) = (a-b)^2 * (a^2 + ab + b^2)*(a+b)"
    using assms 
    by blast

  moreover
  have "(a-b)^2 * (a^2 + ab + b^2)*(a+b) \<ge> 0"
    using assms
    by auto
  
  moreover 
  have "(a^3 - b^3) * (a^2 - b^2) = (a-b)^2 * (a^2 + ab + b^2)*(a+b)"
    using assms 
    by blast

  ultimately
  show ?thesis
    using assms 
    by blast
qed

lemma pomocna2[simp]:
  assumes "\<forall> a b c :: real. a > 0 \<and> b > 0 \<and> c > 0 \<and> a * b * c = 1"
          "(a^3 - b^3) * (a^2 - b^2) \<ge> 0"
  shows "a^5 + b^5 \<ge> a^2*b^2*(a+b)"
 (* using assms 
  by blast*)
proof-
  fix a b c ::real
  have "0 \<le> (a^3 - b^3) * (a^2 - b^2)"
    using assms(1) 
    by blast
  also have "... = a^5 - a^3*b^2 - a^2*b^3 + b^5"
    using assms(1) 
    by blast
  also have "... = a^5 + b^5 - a^3*b^2 - a^2*b^3"
    by auto
  then have "a^3*b^2 + a^2*b^3 \<le> a^5 + b^5"
    using calculation 
    by linarith
  then show ?thesis
    using assms(1) 
    by blast
qed

lemma pomocna3[simp]:
  assumes "\<forall> a b c :: real. a > 0 \<and> b > 0 \<and> c > 0 \<and> a * b * c = 1"
  shows "a*b / (a^5 + b^5 + a*b) \<le> c / (a+b+c)"
  (* using assms 
  by blast*)
proof-
  fix a b c ::real
  have "a*b / (a^5 + b^5 + a*b) \<le> a*b / (a^2*b^2*(a+b) + a*b)"
    using assms 
    by blast
  then have "a*b / (a^5 + b^5 + a*b) \<le> a*b / (a^2*b^2*(a+b) + a*b) * c^2 / c^2"
    using assms 
    by blast
  also have "... = (a*b*c)*c / ((a*b*c)^2 * (a+b) + (a*b*c)*c)"
    using assms 
    by blast
  also have "... = c / (a+b+c)"
    by (simp add: assms)
  then show ?thesis
  using assms 
  by blast
qed

lemma teorija:
  assumes "\<forall> a b c :: real. a > 0 \<and> b > 0 \<and> c > 0 \<and> a * b * c = 1"
  shows "glavni_izraz a b c \<le> 1"
  using assms
proof
  fix a b c ::real
  have "a>0" "b>0" "c>0"
    using assms
    by auto
  then have "0 \<le> (a^3 - b^3) * (a^2 - b^2)"
    by (simp add: assms)
  then have "0 \<le> a^5 - a^3*b^2 - a^2*b^3 +  b^5"
    by (simp add: assms less_eq_real_def)
  then have "a^2*b^2*(a+b) \<le> a^5 + b^5"
    using assms 
    by blast
  then have "a*b / (a^5 + b^5 + a*b) \<le> a*b / (a^2*b^2*(a+b) + a*b)"
    using assms 
    by blast
  then have "a*b / (a^5 + b^5 + a*b) \<le> a*b / (a^2*b^2*(a+b) + a*b) * c^2 / c^2"
    using assms 
    by blast
  also have "... = (a*b*c)*c / ((a*b*c)^2 * (a+b) + (a*b*c)*c)"
    using assms 
    by blast
  also have "... = c / (a+b+c)"
    by (simp add: assms)

  moreover
  have "b*c / (b^5 + c^5 + b*c) \<le> b*c / (b^2*c^2*(b+c) + b*c)"
    using assms 
    by blast
  then have "b*c / (b^5 + c^5 + b*c)  \<le> (b*c / (b^2*c^2*(b+c) + b*c)) * a^2 / a^2"
    using assms 
    by blast
  then have "... =  (a*b*c)*a  / ((a*b*c)^2 * (b+c) + (a*b*c)*a)"
    using assms 
    by blast
  then have "... = a / (a+b+c)"
    using assms 
    by blast

  moreover
   have "c*a / (c^5 + a^5 + c*a) \<le> c*a / (c^2*a^2*(c+a) + c*a)"
    using assms 
    by blast
  then have "c*a / (c^5 + a^5 + c*a)  \<le> (c*a / (c^2*a^2*(c+a) + c*a)) * b^2 / b^2"
    using assms 
    by blast
  then have "... =  (a*b*c)*b  / ((a*b*c)^2 * (c+a) + (a*b*c)*b)"
    using assms 
    by blast
  then have "... = a / (a+b+c)"
    using assms 
    by blast

  ultimately
  have "a*b / (a^5 + b^5 + a*b) + b*c / (b^5 + c^5 + b*c) + a*c / (c^5 + a^5 + a*c) \<le>
  c / (a+b+c) + a / (a+b+c) + b / (a+b+c)"
    using assms 
    by blast
  then show ?thesis
    using assms 
    by blast
qed

(*automatski*)
lemma theorm1:
  assumes "\<forall> a b c :: real. a > 0 \<and> b > 0 \<and> c > 0 \<and> a * b * c = 1"
  shows "a*b / (a^5 + b^5 + a*b) + b*c / (b^5 + c^5 + b*c) + a*c / (c^5 + a^5 + a*c) \<le> 1"
  using assms
  by blast

end