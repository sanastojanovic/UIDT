theory mi15070_Mladen_Dobrasinovic 
  imports Main Complex_Main
begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2017SL.pdf
  Neka su a1, a2,...,an,k i M pozitivni celi brojevi takvi da
  1/a1 + ... + 1/an = k  i a1*a2...an = M.

  Ako je M > 1 dokazimo da je polinom P(x):
  P(x) = M(x + 1)^k - (x+a1)(x+a2)...(x+an)

  Nema pozitivnih korena.
\<close>

definition poly :: "nat list \<Rightarrow> real \<Rightarrow> real" where
  "poly A x = (\<Prod>n < length A. (x + real (A ! n)))"

definition poly2 :: "real \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "poly2 M A k x = M * (x + 1) ^ k - (poly A x)"

(*
PROBLEM: Ovde sam pokusavao da dokazem tvrdnju, ali mi se cini da nije imalo smisla pa sam samo
ostavio sorry. Ne znam kako bih uradio ovaj dokaz. U Isabelle-u ima slicna teorema za pow, ali ne za
root, sto je meni potrebno.
*)

lemma prod_of_sum_list:
  fixes x :: "real" and a :: "nat list" and k :: "nat"
  assumes "(\<Sum>n < length a. 1 / real (a ! n)) =  k"
  shows "(\<Prod>n < length a. root (a ! n) x) = x ^ k"
  using assms 
  sorry

(*
PROBLEM: Ovde sam raspisao pokusaj dokaza specificnog slucaja koji nam je potreban, ali nisam
siguran u ispravnost pokusaja. U Isabelle-u nisam nasao teoreme koja bi ovo potvrdila.
*)
lemma AM_GM_N:
  fixes x :: "real" and n :: "nat" and m :: "nat"
  assumes "n \<ge> 1 \<and> x > 0"
  shows "(x + 1 * (real n)) / (real n) \<ge> root (n) (x + 1)"
proof-
  have foo: "x + 1 * real n \<ge> 0 \<and> x + 1 \<ge> 0"
    using assms
    by auto
  then have "power ((x + 1 * (real n)) / (real n)) n \<ge> power (root (n) (x + 1)) n \<longrightarrow> ?thesis"
    by (smt (verit, best) assms divide_nonneg_pos less_le_trans of_nat_0_less_iff power_mono real_root_pos_unique zero_less_one)
  also have "power (root (n) (x + 1)) n = x + 1"
    using assms foo
    by auto
  finally have "power ((x + 1 * (real n)) / (real n)) n \<ge> (x + 1) \<longrightarrow> ?thesis"
    by auto
  also have "power ((x + 1 * (real n)) / (real n)) n \<ge> (x + 1)"
  proof-
    have "power ((x + 1 * (real n)) / (real n)) n = power (x + 1 * real n) n / power (real n) n"
    proof-
      have "(x + 1 * (real n)) / (real n) \<ge> 0"
        using assms foo
        by auto
      then show ?thesis
        using assms foo Power.field_class.power_divide
        by auto
    qed
    then have "power (x + 1 * real n) n / power (real n) n \<ge> x + 1"
    proof-
      have "power (real n) n > 0"
        using assms
        by auto
      then have "(power (x + real n) n \<ge> (x + 1) * power (real n) n) \<longrightarrow> (power (x + 1 * real n) n / power (real n) n \<ge> x + 1)"
        using assms foo
        by (simp add: mult_imp_le_div_pos)
      also have "power (x + real n) n \<ge> (x + 1) * power (real n) n"
        sorry
      finally show ?thesis
        by auto    
    qed
    then show ?thesis
    using \<open>((x + 1 * real n) / real n) ^ n = (x + 1 * real n) ^ n / real n ^ n\<close> \<open>x + 1 \<le> (x + 1 * real n) ^ n / real n ^ n\<close> by presburger
  qed
  then show ?thesis
  using calculation by blast
qed



lemma Alg1:   
  fixes x :: "real" and A :: "nat list" and M :: "nat" and k :: "nat"
  assumes "prod_list A > 0" and
          "(\<forall> i::nat. i < (length A) \<longrightarrow> A ! i \<ge> 1)" and
          " M > 0"  and
          " k > 0"  and
          " x > 0 " and
          "(\<Sum>n < length A. 1 / real (A ! n)) =  k" and
          " sum_list (map (inverse) A) = k " and
          " (\<Prod> n < length A. real(A ! n))= M "
        shows "poly2 M A k x \<noteq> 0"
proof-
  fix i :: "nat"
  have  "i < (length A) \<longrightarrow> (real (A ! i)) * (root (A ! i) (x + 1) ) \<le> x + (real (A ! i))"
  proof (cases "i < length A")
    case True
    then have "A ! i \<ge> 1"
      using assms
      by auto
    then have "(x + ((1) * (real (A ! i)))) / (A ! i) \<ge> root (A ! i) (x + 1)"
      using assms AM_GM_N
      by auto
    then show ?thesis
      using assms
      by (smt (verit, ccfv_SIG) \<open>1 \<le> A ! i\<close> less_le_trans mult.commute of_nat_0_less_iff pos_divide_less_eq zero_less_one)
  next
    case False
    then show ?thesis
      by auto
  qed
  then have "(\<Prod>n < length A.(real (A ! n)) * root (A ! n) (x + 1)) \<le> (\<Prod>n < length A.(x + real (A ! n)))"
    using assms prod_mono
    by (smt (verit, best) AM_GM_N lessThan_iff less_le_trans mult.commute mult_nonneg_nonneg of_nat_0_less_iff pos_divide_less_eq real_root_pos_pos_le zero_less_one)
  then have "(\<Prod>n < length A.(real (A ! n)) * root (A ! n) (x + 1)) - (\<Prod>n < length A.(x + real (A ! n))) \<le> 0"
    by simp
  then have "M * (\<Prod>n < length A. root (A ! n) (x + 1)) - (\<Prod>n < length A.(x + real (A ! n))) \<le> 0"
    using \<open>(\<Prod> n < length A. real (A ! n))= M\<close> Groups_Big.comm_monoid_mult_class.prod.distrib
    by (simp add: prod.distrib)
  then have "M * (x + 1) ^ k - (\<Prod>n < length A.(x + real (A ! n))) \<le> 0"
    using assms 
    by (auto simp add: prod_of_sum_list)
  then have almost: "poly2 M A k x \<le> 0"
    unfolding poly2_def poly_def
    using assms
    by blast
(*
    PROBLEM: Ovde dobijamo da je polinom za x > 0, manje-jednak nuli, u resenju pise otprilike:
    jednakost u prethodnom proizvodu vazi samo u slucaju kada su svi cinioci jednaki, odnosno
    ai = 1 za sve i, a to ne vazi zbog odredjedjenih cinjenica. Smatram da treba dokazati jacu
    tvrdnju, odnosno poly2 M A k x < 0, ali nisam siguran kako to uraditi tacno.
*)
  then show ?thesis
    using almost
    sorry
qed


end
