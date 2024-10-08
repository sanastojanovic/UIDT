theory mi15160_Dusan_Pantelic
  imports Complex_Main
begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2016SL.pdf
A5.
(a) Dokazati da za svaki pozitivni ceo broj n, postoji razlomak a/b
gde su a i b celi brojevi za koje vazi 0 < b \<le>  n^(1/2) + 1 i
n^(1/2) \<le> a/b \<le> (n+1)^(1/2)

(b) Dokazati da postoji beskonacno mnogo pozitivnih celih brojeva n tako da ne postoji razlomak a/b
gde su a i b celi brojevi za koje vazi 0 < b \<le>  n^(1/2) i
n^(1/2) \<le> a/b \<le> (n+1)^(1/2)
\<close>

lemma A5_a:
  fixes n::nat and a::int and b::int
  assumes "r^2\<ge>n \<and> (r+1)^2 \<le> n \<and> n = r^2 + s \<and> s\<ge>0 \<and> s \<le> 2*r"
  shows "\<forall> n. \<exists>a b. 0<b \<and> b\<le>sqrt n + 1 \<and> sqrt n \<le> a/b \<and> a/b \<ge> sqrt (n+1)"
  using assms
proof (cases "s mod 2 = 0")
  case True
  then have "n \<le>  r^2 + s + (s/2*r)^2" by (simp add: assms)
  then have "... \<le> r^2 + s + 1" using assms by fastforce
  then have "... = n+1" using assms by auto
  then have "sqrt n \<le> r + (s/2*r) " using assms by fastforce
  then have "... \<le> sqrt (n+1)" using assms by fastforce
  then have "a/b =  (r^2 + (s/2))/r" using assms by fastforce
  then have "b \<ge> 0 \<and> b \<le> sqrt n + 1" using assms by force
  then show ?thesis using assms by auto
next
  case False
  then have "n =  (r+1)^2 - (2*r - s + 1)" 
    by (metis assms diff_add_inverse diff_is_0_eq' mod_less_eq_dividend not_mod_2_eq_1_eq_0 not_numeral_le_zero numerals(1))
  then have "... \<le> (r+1)^2 - (2*r - s + 1) + ((2*r + 1 - s)/(2*(r+1)))^2" by auto
  then have "... \<le> (r+1)^2 - (2*r - s + 1) + 1" using assms by fastforce
  then have "... = n+1" by (simp add: \<open>n = (r + 1)\<^sup>2 - (2 * r - s + 1)\<close>)
  then have "sqrt n \<le> r + 1 - (2*r + 1 - s)/(2*(r+1))" using assms by auto
  then have "... \<le> sqrt (n+1)" using assms by auto
  then have "a/b = ((r+1)^2 - r + ((s-1)/2))/(r+1)" using assms by (metis False assms diff_0_eq_0 diff_add_inverse diff_is_0_eq' modulo_nat_def)
  then have "b \<ge> 0 \<and> b \<le> sqrt n + 1" using assms by force
  then show ?thesis using assms by auto
qed

lemma A5_b:
  fixes n::nat and a::int and b::int and r::nat
  assumes "S = {n.  \<nexists>a b. 0<b \<and> b\<le>sqrt n  \<and> sqrt n \<le> a/b \<and> a/b \<ge> sqrt (n+1)}"
  assumes " R = {r . \<nexists>a b. 0<b \<and> b\<le>sqrt (r^2+1)  \<and> sqrt (r^2+1) \<le> a/b \<and> a/b \<ge> sqrt (r^2+2)}"
shows "infinite S"
  using assms
proof- 
qed