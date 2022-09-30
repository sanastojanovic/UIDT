theory mi18465_Vladimir_Mandic

imports Complex_Main "HOL-Number_Theory.Residues"

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2017SL.pdf

Zadatak: Number Theory N5

Tekst zadatka:
Find all pairs (p,q) of prime numbers p > q for which the number
((p+q)^(p+q)*(p-q)^(p-q)-1)/((p+q)^(p-q)*(p-q)^(p+q)-1) is an integer

Odgovor:
Jedini takav par je (3,2)
\<close>

(*Seminarski 1*)
lemma
  assumes "prime p" "prime q" "p > q" "\<exists>k::nat. ((p+q)^(p+q)*(p-q)^(p-q)-1)div((p+q)^(p-q)*(p-q)^(p+q)-1) = k"
  shows "p = 3" "q = 2"
  sorry

(*Seminarski 2*)

(*Uvodimo konstantu M*)
definition M  where
  "M p q = (p+q)^(p-q)*(p-q)^(p+q)-1"

(*dokaz da je M definisano sa M=(p+q)^(p-q)*(p-q)^(p+q)-1 uzajamno prosto sa (p-q)*)
lemma M_coprime_P_Minus_Q[simp]:
  assumes "p > q" "prime p" "prime q" 
  shows "coprime (M p q) (p-q)"
  using assms
  unfolding M_def
  by (metis coprime_diff_one_left_nat coprime_mult_right_iff coprime_power_right_iff less_add_same_cancel2 nat_0_less_mult_iff not_less_zero trans_less_add1 zero_less_diff zero_less_power)

(*dokaz da je M definisano sa M=(p+q)^(p-q)*(p-q)^(p+q)-1 uzajamno prosto sa (p+q)*)
lemma M_coprime_P_Plus_Q[simp]:
  assumes "p > q" "prime p" "prime q" 
  shows "coprime (M p q) (p+q)"
  using assms
  unfolding M_def
  by (metis coprime_diff_one_left_nat coprime_mult_right_iff coprime_power_right_iff less_add_same_cancel2 nat_0_less_mult_iff not_less_zero trans_less_add1 zero_less_diff zero_less_power)

(*pomocna lema koriscena u lemi glavna1(u 1. koraku dokaza ove leme)*)
lemma pomocna1_1:
  assumes "\<exists>k::nat. ((p+q)^(p+q)*(p-q)^(p-q)-1) = k*(M p q)"
  shows "[(p+q)^(p+q)*(p-q)^(p-q)-1 = (p+q)^(p-q)*(p-q)^(p+q)-1](mod M p q)"
proof-
  from assms(1) obtain k where "((p+q)^(p+q)*(p-q)^(p-q)-1) = k*(M p q)" by auto
  from this have "((p+q)^(p+q)*(p-q)^(p-q)-1) = k * ((p+q)^(p-q)*(p-q)^(p+q)-1)" unfolding M_def by auto
  also have "[\<dots> = ((p+q)^(p-q)*(p-q)^(p+q)-1)](mod M p q)" unfolding M_def by (simp add: cong_def)    
  finally show ?thesis .
qed

(*2 pomocne leme kako bismo u lemi glavna1 sa leve strane dobili (p+q)^(2*q)*)
lemma pomocna1_2:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)powi(p+q)*(p-q)powi(p-q)-1 = k*(M p q)"
  shows "(p+q)powi(p+q)*(p+q)powi(q-p) = (p+q)powi(2*q)"
  using assms [[show_types]]
  by (smt (verit, best) of_nat_0 of_nat_less_iff power_int_add trans_less_add1)
  

lemma pomocna1_3: 
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)powi(p+q)*(p-q)powi(p-q)-1 = k*(M p q)"
  shows "(p-q)powi(p-q)*(p-q)powi(q-p) = 1"
  using assms [[show_types]]
  by (smt (verit) less_imp_of_nat_less of_nat_0 power_int_0_right power_int_add zero_less_diff)

(*2 pomocne leme kako bismo u lemi glavna1 sa desne strane dobili (p-q)^(2*q) *)
lemma pomocna1_4:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)powi(p+q)*(p-q)powi(p-q)-1 = k*(M p q)"
  shows "(p+q)powi(p-q)*(p+q)powi(q-p) = 1"
  using assms [[show_types]]
  by (smt (verit) less_add_same_cancel2 less_imp_of_nat_less of_nat_0 power_int_0_right power_int_add prime_gt_0_nat)

lemma pomocna1_5:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)powi(p+q)*(p-q)powi(p-q)-1 = k*(M p q)"
  shows "(p-q)powi(p+q)*(p-q)powi(q-p) = (p-q)powi(2*q)"
  using assms [[show_types]]
  by (smt (verit) diff_is_0_eq linorder_not_le of_nat_eq_0_iff power_int_add)

(*kombinacija leme pomocna1_2 i leme pomocna1_3
(p+q)powi(p+q)*(p+q)powi(q-p)*(p-q)powi(p-q)*(p-q)powi(q-p) = (p+q)powi(2*q)*1
*)
lemma pomocna1_2_3[simp]:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)powi(p+q)*(p-q)powi(p-q)-1 = k*(M p q)"
  shows "(p+q)powi(p+q)*(p+q)powi(q-p)*(p-q)powi(p-q)*(p-q)powi(q-p) = (p+q)powi(2*q)*1"
  using pomocna1_2 pomocna1_3 assms [[show_types]]
  by force

(*kombinacija leme pomocna1_4 i pomocna1_5*)
lemma pomocna1_4_5[simp]:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)powi(p+q)*(p-q)powi(p-q)-1 = k*(M p q)"
  shows "(p+q)powi(p-q)*(p+q)powi(q-p)*(p-q)powi(p+q)*(p-q)powi(q-p) = 1*(p-q)powi(2*q)"
  using assms [[show_types]]
  using pomocna1_4 pomocna1_5 by auto

(*Problem - kada hocu da dobijem oblik 
(p+q)powi(2*q)*1 + k1*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p) = 1*(p-q)powi(2*q) + k2*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p)
Hocu da vratim "nazad" u formu (p+q)^(2*q) = (p-q)^(2*q) (mod M p q)
Problem je u radu sa stepenom*)

lemma p1:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)^(p+q)*(p-q)^(p-q)-1 = k*(M p q)"
  shows "(p+q)powi((p+q)+(q-p))*(p-q)powi((p-q)+(q-p)) = (p+q)powi(p+q+q-p)*(p-q)powi(p-q+q-p)"
  using assms
  by simp

lemma p2:
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)^(p+q)*(p-q)^(p-q)-1 = k*(M p q)"
  shows "(p+q)powi((p-q)+(q-p))*(p-q)powi((p+q)+(q-p)) = (p+q)powi(p-q+q-p)*(p-q)powi(p+q+q-p)"
  using assms
  by simp

lemma glavna1:
  fixes p q::nat
  assumes "p > q" "prime p" "prime q" "\<exists>k::nat. (p+q)^(p+q)*(p-q)^(p-q)-1 = k*(M p q)"
  shows "[(p+q)^(2*q) = (p-q)^(2*q)](mod M p q)"
proof-
  have "[(p+q)^(p+q)*(p-q)^(p-q)-1 = (p+q)^(p-q)*(p-q)^(p+q)-1](mod M p q)"
    using pomocna1_1
    using assms(4)
    by auto
  from this have "[(p+q)^(p+q)*(p-q)^(p-q) = (p+q)^(p-q)*(p-q)^(p+q)](mod M p q)"
    using assms
    by (smt (verit, best) One_nat_def Suc_pred cong_add_lcancel_nat less_add_same_cancel2 nat_0_less_mult_iff plus_1_eq_Suc trans_less_add1 zero_less_diff zero_less_power)
  from this obtain k1 k2 where "(p+q)^(p+q)*(p-q)^(p-q) + k1*(M p q) = (p+q)^(p-q)*(p-q)^(p+q) + k2*(M p q)"
    using cong_iff_lin_nat 
    by metis
  from this have "(p+q)powi(p+q)*(p-q)powi(p-q) + k1*(M p q) = (p+q)powi(p-q)*(p-q)powi(p+q)+k2*(M p q)"
    by (metis (mono_tags, lifting) of_nat_add of_nat_mult of_nat_power power_int_of_nat)
  from this have "(p+q)powi(p+q)*(p-q)powi(p-q)*(p+q)powi(q-p)*(p-q)powi(q-p) + k1*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p)= (p+q)powi(p-q)*(p-q)powi(p+q)*(p+q)powi(q-p)*(p-q)powi(q-p) + k2*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p)"
    by (metis (mono_tags, lifting) ring_class.ring_distribs(2))
  from this have "(p+q)powi(p+q)*(p+q)powi(q-p)*(p-q)powi(p-q)*(p-q)powi(q-p) + k1*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p) = (p+q)powi(p-q)*(p+q)powi(q-p)*(p-q)powi(p+q)*(p-q)powi(q-p) + k2*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p)"
    using [[show_types]]
    by (smt (verit, del_insts) mult.assoc mult.commute)
  from this have "(p+q)powi((p+q)+(q-p))*(p-q)powi((p-q)+(q-p)) + k1*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p) = (p+q)powi((p-q)+(q-p))*(p-q)powi((p+q)+(q-p))+k2*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p)"
    using assms(1) int_ops(6) less_imp_of_nat_less mult.right_neutral nat_int of_nat_0 power_int_0_right by force
  from this have "(p+q)powi((p+q)+(q-p))*(p-q)powi((p-q)+(q-p)) - (p+q)powi((p-q)+(q-p))*(p-q)powi((p+q)+(q-p)) = k2*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p) - k1*(M p q)*(p+q)powi(q-p)*(p-q)powi(q-p)"
    by linarith
  from this have "[((p+q)^((p+q)+(q-p))*(p-q)^((p-q)+(q-p)) - (p+q)^((p-q)+(q-p))*(p-q)^((p+q)+(q-p))) = 0](mod M p q)"
    by (smt (z3) \<open>[(p + q) ^ (p + q) * (p - q) ^ (p - q) = (p + q) ^ (p - q) * (p - q) ^ (p + q)] (mod M p q)\<close> add_diff_inverse_nat assms(1) cong_def cong_diff_iff_cong_0_nat diff_add_zero diff_is_0_eq less_imp_of_nat_less mult.right_neutral power_0 power_add)
  (* from this have "[((p+q)^(2*q)*(p-q)^(0) - (p+q)^(0)*(p-q)^(2*q)) = 0](mod M p q)" *)
       
  from this show ?thesis sorry
qed

(*Ako je q \<ge> 5 i q je prost broj onda q mora biti neparno jer je 
jedini prost broj koji nije neparan 2*)
lemma pomocna1_neparno_M:
  fixes q::nat
  assumes "q \<ge> 5" "prime q"
  shows "odd q"
  using assms
  by (metis numeral_le_iff primes_dvd_imp_eq semiring_norm(68) semiring_norm(72) semiring_norm(88) two_is_prime_nat verit_la_disequality)

(*Ako je q\<ge> 5,p i q su prosti brojevi i p > q,onda p mora biti neparan broj
Objasnjenje:
Kao sto je malopre napomenuto jedini prost broj koji nije neparan je 2,a kako
je p > q,a q \<ge> 5 sledi da p ne moze biti 2 odakle sledi da je p neparno(buduci da je p prost)*)
lemma pomocna2_neparno_M:
  fixes p q::nat
  assumes "q \<ge> 5" "prime p" "prime q" "p > q"
  shows "odd p"
  using assms
  by (simp add: prime_odd_nat)

(*zbir 2 neparna broja je paran broj,a paran broj na svaki stepen 
(osim 0) je paran broj,ali kako je p > q onda njihova razlika ne moze biti 0*)
lemma pomocna3_neparno_M:
  fixes p q::nat
  assumes "odd p" "odd q" "p > q"
  shows "even((p+q)^(p-q))"
  using assms
  by auto

(*Objasnjenje: analogno prethodnom*)
lemma pomocna4_neparno_M:
  fixes p q::nat
  assumes "odd p" "odd q" "p > q"
  shows "even((p-q)^(p+q))"
  using assms
  by simp

(*Objasnjenje: sledi direktno iz prethodno pokazanog. 
Pokazali smo da su (p+q)^(p-q) i (p-q)^(p+q) parni brojevi.Kada od parnog broja oduzmemo 1
dobijamo neparni te tvrdjenje trivijalno sledi*)
lemma neparno_M:
  fixes p q::nat
  assumes "q \<ge> 5" "prime p" "prime q" "p > q"
  shows "odd((p+q)^(p-q)*(p-q)^(p+q)-1)"
  using assms
  by (simp add:pomocna1_neparno_M 
               pomocna2_neparno_M 
               pomocna3_neparno_M 
               pomocna4_neparno_M)

lemma r_gte_3:
  fixes p q r::nat
  assumes "q \<ge> 5" "prime p" "prime q" "prime r" "p > q" "odd(M p q)" "r dvd (M p q)"
  shows "r \<ge> 3"
  by (smt (verit, best) assms(4) assms(6) assms(7) dbl_simps(3) dbl_simps(5) int_eq_iff_numeral nat_int_comparison(3) numeral_Bit1 one_eq_numeral_iff prime_ge_2_nat)


lemma Mala_Fermaova_teorema:
  fixes p a::nat
  assumes "prime p" and "\<not>(p dvd a)"
  shows "[a^(p-1) = 1](mod p)"
  using assms
proof-
  from assms prime_imp_coprime have "coprime a p"
    using coprime_commute by blast
  from this have "[a^(totient p) = 1] (mod p)"
    by(rule euler_theorem)
  also have "totient p = p - 1"
    by(rule totient_prime)(rule assms)
  finally show ?thesis .
qed



end
