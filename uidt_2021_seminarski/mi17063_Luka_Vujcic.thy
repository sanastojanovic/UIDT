theory mi17063_Luka_Vujcic
  imports Complex_Main
begin
text\<open>
  https://www.imo-official.org/problems/IMO2013SL.pdf
  Zadatak: Number theory N2
  Tekst zadatka: Dokazati da za svaka dva prirodna broja k i n postoji
  k prirodnih brojeva m1,m2,...,mk (ne obavezno razlicitih) takvih da je
  1+ (2^k-1)/n=(1+1/m1)(1+1/m2)...(1+1/mk)
  Napomena: 0 se ne smatra prirodnim brojem u ovom razmatranju
\<close>
(*Seminarski 1*)
lemma
  fixes k n::nat
  assumes "k>0" "n>0"
  shows "\<exists> m::nat list. prod_list m \<noteq> 0 \<and> length m=k \<and> 1+ (2^k-1) / n=prod_list (map (\<lambda> x. 1+1 / x) m)"
  sorry

(*Seminarski  2*)
lemma
  fixes k n::nat
  assumes "k>0" "n>0"
  shows "\<exists> m::nat list. prod_list m \<noteq> 0 \<and> length m=k \<and> 1+ (2^k-1) / n=prod_list (map (\<lambda> x. 1+1 / x) m)"
  using assms
proof (induction k arbitrary:n)
  case 0
    then show ?case by simp
  next
  case (Suc k)
  note ih=this
  show ?case
  proof (cases "Suc k=1")    
    case True
    note k_value=this
    show ?thesis
    proof-
      obtain m where "m=[n::nat]" by  auto
      note m_list=this
      then have "prod_list m \<noteq> 0"  "length m = Suc k" "1 + (2 ^ Suc k - 1) / real n = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)" using ih(3) k_value m_list by auto
      then show ?thesis by auto
    qed
  next
    case False
    then show ?thesis
    proof (cases "even n")
      case True
      then show ?thesis
      proof
        obtain t where "n=2*t" using True by auto
        note double_value=this
        show "\<exists>m. prod_list m \<noteq> 0 \<and> length m = Suc k \<and> 1 + (2 ^ Suc k - 1) / real n = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)"
        proof-
          obtain m where  "prod_list m\<noteq>0 \<and> length m=k \<and> 1+(2^k-1)/real (t)= (\<Prod>x\<leftarrow>m. 1 + 1 / real x)" using assms ih by (metis False One_nat_def double_value nat_0_less_mult_iff nat_neq_iff not_less_eq)
          have "1 + (2 ^ Suc k - 1) / real n = 1+ (2* 2^k -1 ) / real n" by auto
          also have "\<dots>= 1+ (2* 2^k - 1 ) / real (2*t)" using double_value by auto
          also have "\<dots>= 2*t/real (2*t)+ (2* 2^k - 1 ) / real (2*t)"  using assms(2) double_value using ih(3) by auto
          also have "\<dots>= (2* 2^k - 1+2*t ) / real (2*t)" by (smt (verit, best) \<open>1 + (2 * 2 ^ k - 1) / real (2 * t) = real (2 * t) / real (2 * t) + (2 * 2 ^ k - 1) / real (2 * t)\<close> add_diff_inverse_nat add_divide_distrib calculation double_value less_one nat.simps(3) of_nat_Suc of_nat_add of_nat_power one_add_one plus_1_eq_Suc power_Suc2 power_commutes power_eq_0_iff)
          also have "\<dots>=(2*2^k+2*t-1)/real(2*2^k+2*t-2)*(2*2^k+2*t-2)/real(2*t)" by (smt (verit, best) Nat.diff_cancel Suc_1 add.right_neutral add_diff_inverse_nat add_less_cancel_left diff_add_inverse double_value ih(3) less_one mult_eq_0_iff nat_1_eq_mult_iff nonzero_divide_eq_eq of_nat_eq_0_iff plus_1_eq_Suc power_eq_0_iff)
          also have "\<dots>=(2*2^k+2*t-2+1)/real(2*2^k+2*t-2)*(2*2^k+2*t-2)/real (2*t)" by auto
          also have "\<dots>=((2*2^k+2*t-2)/real(2*2^k+2*t-2)+1/real(2*2^k+2*t-2))*(2*2^k+2*t-2)/real (2*t)" by (simp add: add_divide_distrib)
          also have "\<dots>=(1+1/real(2*2^k+2*t-2))*(2*2^k+2*t-2)/real (2*t)" by simp
          also have "\<dots>=(1+1/real(2*2^k+2*t-2))*2*(2^k+t-1)/real (2*t)" by (smt (verit, del_insts) diff_mult_distrib2 distrib_left distrib_right mult_2 nat_1_add_1 of_nat_add)
          also have "\<dots>=(1+1/real(2*2^k+2*t-2))*(2^k+t-1)/real (t)" using algebra_simps by (simp add: distrib_left mult.commute add_divide_distrib)
          also have "\<dots>=(1+1/real(2*2^k+2*t-2))*((2^k-1)/real (t)+t/real (t))" using algebra_simps by (smt (verit, best) Suc_1 add_diff_inverse_nat add_divide_distrib add_less_cancel_left double_value ih(3) less_one mult_2 numeral_power_less_of_nat_cancel_iff of_nat_0 of_nat_1 of_nat_add of_nat_numeral of_nat_power plus_1_eq_Suc times_divide_eq_right)
          also have "\<dots>=(1+1/real(2*2^k+2*t-2))*(1+(2^k-1)/real (t))" using assms(2) double_value using ih(3) by fastforce
          also have "\<dots>=(1+1/real(2*2^k+2*t-2))*(\<Prod>x\<leftarrow>m. 1 + 1 / real x)" using \<open>prod_list m \<noteq> 0 \<and> length m = k \<and> 1 + (2 ^ k - 1) / real t = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)\<close> by presburger
          also have "\<dots>=(\<Prod>x\<leftarrow>(2*2^k+2*t-2)#m. 1 + 1 / real x)"  by auto
          let ?l="(2*2^k+2*t-2)#m"
          have 1:"prod_list ?l\<noteq>0" using \<open>1 + (2 * 2 ^ k - 1) / real (2 * t) = real (2 * t) / real (2 * t) + (2 * 2 ^ k - 1) / real (2 * t)\<close> \<open>prod_list m \<noteq> 0 \<and> length m = k \<and> 1 + (2 ^ k - 1) / real t = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)\<close> \<open>real (2 * 2 ^ k - 1 + 2 * t) / real (2 * t) = real (2 * 2 ^ k + 2 * t - 1) / real (2 * 2 ^ k + 2 * t - 2) * real (2 * 2 ^ k + 2 * t - 2) / real (2 * t)\<close> by auto
          have 2:"length ?l = Suc k" by (simp add: \<open>prod_list m \<noteq> 0 \<and> length m = k \<and> 1 + (2 ^ k - 1) / real t = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)\<close>)
          have 3:"1 + (2 ^ Suc k - 1) / real n = (\<Prod>x\<leftarrow>?l. 1 + 1 / real x)" using \<open>(1 + 1 / real (2 * 2 ^ k + 2 * t - 2)) * (\<Prod>x\<leftarrow>m. 1 + 1 / real x) = (\<Prod>x\<leftarrow>(2 * 2 ^ k + 2 * t - 2) # m. 1 + 1 / real x)\<close> calculation by presburger
          from 1 2 3 have "prod_list ?l \<noteq> 0 \<and> length  ?l = Suc k \<and> 1 + (2 ^ Suc k - 1) / real n = (\<Prod>x\<leftarrow> ?l. 1 + 1 / real x)" by auto
          then show ?thesis by blast
        qed
      qed
    next
      case False
      then show ?thesis
      proof-
        obtain t where "n=2*t-1" using False by (metis add_diff_cancel_right' evenE even_plus_one_iff)
        show "\<exists>m. prod_list m \<noteq> 0 \<and> length m = Suc k \<and> 1 + (2 ^ Suc k - 1) / real n = (\<Prod>x\<leftarrow>m. 1 + 1 / real x) "
        proof-
          obtain m where "prod_list m\<noteq>0 \<and> length m=k \<and> 1+(2^k-1)/real (t)= (\<Prod>x\<leftarrow>m. 1 + 1 / real x)" using Suc.IH \<open>n = 2 * t - 1\<close> ih(3) by fastforce
          have "1 + (2 ^ Suc k - 1) / real n = 1+ (2* 2^k -1 ) / real n" by auto
          also have "\<dots>= 1+ (2* 2^k -1 ) / real (2*t-1)"using \<open>n = 2 * t - 1\<close> by blast
          also have "\<dots>=(2*t-1)/real (2*t-1)+ (2* 2^k -1 ) / real (2*t-1)" using \<open>n = 2 * t - 1\<close> ih(3) by auto
          also have "\<dots>=(2* 2^k -1+2*t-1 ) / real (2*t-1)" using add_diff_inverse_nat add_divide_distrib calculation less_one nat.simps(3) of_nat_Suc of_nat_add of_nat_power one_add_one plus_1_eq_Suc power_Suc2 power_commutes power_eq_0_iff by (smt (verit, best) One_nat_def \<open>1 + (2 * 2 ^ k - 1) / real (2 * t - 1) = real (2 * t - 1) / real (2 * t - 1) + (2 * 2 ^ k - 1) / real (2 * t - 1)\<close> \<open>n = 2 * t - 1\<close> add_is_0 ih(3) nat_add_left_cancel_less of_nat_mult zero_less_diff)
          also have "\<dots>=(2* 2^k -1+2*t-1 )/real(2*t)*(2*t)/real(2*t-1)" by simp
          also have "\<dots>=(2*2^k +2*t-2 )/real(2*t)*(2*t)/real(2*t-1)" by auto
          also have "\<dots>=2*(2^k +t-1 )/real(2*t)*(2*t)/real(2*t-1)" by auto
          also have "\<dots>=(2^k +t-1 )/real(t)*(2*t)/real(2*t-1)" by auto
          also have "\<dots>=(2^k +t-1 )/real(t)*(2*t-1+1)/real(2*t-1)" by (metis One_nat_def Suc_eq_plus1 \<open>n = 2 * t - 1\<close> add_diff_inverse_nat ih(3) less_one not_add_less1 plus_1_eq_Suc zero_less_diff)
          also have "\<dots>=(2^k +t-1 )/real(t)*((2*t-1)/real(2*t-1)+1/real(2*t-1))" by (metis (no_types, lifting) add_divide_distrib of_nat_1 of_nat_add times_divide_eq_right)
          also have "\<dots>=(2^k +t-1 )/real(t)*(1+1/real(2*t-1))" by auto
          also have "\<dots>=(t/real(t)+(2^k-1 )/real(t))*(1+1/real(2*t-1))" using algebra_simps by (smt (verit) \<open>n = 2 * t - 1\<close> add.right_neutral add_diff_cancel_left add_diff_inverse_nat add_divide_distrib add_less_cancel_right add_mono_thms_linordered_field(5) cancel_comm_monoid_add_class.diff_cancel ih(3) less_one mult_cancel_right nat_1_add_1 neq0_conv of_nat_1 of_nat_add of_nat_power zero_less_diff)
          also have "\<dots>=(1+(2^k-1 )/real(t))*(1+1/real(2*t-1))" using \<open>n = 2 * t - 1\<close> ih(3) by force
          also have "\<dots>=(1+1/real(2*t-1))*(\<Prod>x\<leftarrow>m. 1 + 1 / real x)" by (simp add: \<open>prod_list m \<noteq> 0 \<and> length m = k \<and> 1 + (2 ^ k - 1) / real t = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)\<close>)
          also have "\<dots>=(\<Prod>x\<leftarrow>(2*t-1)#m. 1 + 1 / real x)" by auto
          let ?l="(2*t-1)#m"
          have 1:"prod_list ?l \<noteq> 0" by (metis \<open>n = 2 * t - 1\<close> \<open>prod_list m \<noteq> 0 \<and> length m = k \<and> 1 + (2 ^ k - 1) / real t = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)\<close> ih(3) mult_eq_0_iff nat_neq_iff prod_list.Cons)
          have 2: "length ?l = Suc k" by (simp add: \<open>prod_list m \<noteq> 0 \<and> length m = k \<and> 1 + (2 ^ k - 1) / real t = (\<Prod>x\<leftarrow>m. 1 + 1 / real x)\<close>)
          have 3: "1 + (2 ^ Suc k - 1) / real n = (\<Prod>x\<leftarrow>?l. 1 + 1 / real x)" using \<open>(1 + 1 / real (2 * t - 1)) * (\<Prod>x\<leftarrow>m. 1 + 1 / real x) = (\<Prod>x\<leftarrow>(2 * t - 1) # m. 1 + 1 / real x)\<close> calculation by presburger
          from 1 2 3 show ?thesis by blast
        qed
      qed
    qed
  qed
qed
end
