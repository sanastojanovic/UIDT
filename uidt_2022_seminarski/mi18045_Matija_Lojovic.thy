theory mi18045_Matija_Lojovic
  imports Complex_Main
begin

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

text\<open>
Link: https://www.imo-official.org/problems/IMO2007SL.pdf
Number Theory: N1

Find all pairs (k, n) of positive integers for which 7^k − 3^n divides k^4 + n^2.

Answer: (2, 4)

\<close>
(* 1. Seminarski*)
lemma task:
  fixes n k :: nat
  assumes "k>0 \<and> n>0" "7^k - 3^n dvd k^4 + n^2"
  shows "k = 2 \<and> n = 4"
  sorry


(*2. seminarski*)

(* Najpre predpostavljamo da postoje k i n za koje vazi 
  7^k - 3^n dvd k^4 + n^2
*)

(* Dokazujemo da je 7^k - 3^n parno *)
lemma even_7k_3n:
  fixes n k :: nat
  shows"even ((7::int)^k - 3^n)"
  by simp 

(* Posto je 7^k - 3^n parno, iz toga sledi da je i 4^k + n^2 parno *)
lemma even_k4_n2:
  fixes n k :: nat
  assumes "(7::int)^k - 3^n dvd int(k^4 + n^2)"
  shows"even (k^4 + n^2)"
  using assms
  by (meson dvd_trans even_7k_3n even_of_nat)

(* Posto je k^4 + n^2 parno, k i n moraju biti iste parnosti *)
lemma same_parity:
  fixes n k :: nat
  assumes "even (k^4 + n^2)"
  shows"even k \<longleftrightarrow> even n"
  using assms
  by simp

(* Na dalje pretpostavljamo da su k i n neparni brojevi i dokazujemo suprotno *)

(* Pomocna lema koja nam daje n^2 mod 4 *)
lemma mod_4_n:
  fixes n::nat
  assumes"odd n"
  shows"(n^2) mod 4 = 1"
  using assms
proof-
  have "\<exists>x. n = 2*x + 1" using assms by (meson oddE)
  then obtain x where "n = 2*x + 1" by auto
  then have "n^2 - 1 = (2*x + 1)^2 - 1" by auto
  then have "\<dots> = 4*(x*x + x)" by (auto simp add:power2_eq_square)
  from this have "n^2 = 4*(x*x + x) + 1" by (simp add: \<open>n = 2 * x + 1\<close> power2_eq_square)
  from this show "(n^2) mod 4 = 1" by auto
qed

(* Pomocna lema koja nam daje k^4 mod 4 *)
lemma mod_4_k:
  fixes k::nat
  assumes"odd k"
  shows"(k^4) mod 4 = 1"
  using assms
  by (metis even_power mod_4_n power2_eq_square power_numeral_even)

(* Kako je k^4 mod 4 = 1 i n^2 mod 4 = 1, iz toga sledi da je 
  (k^4 + n^2) mod 4 = 2 
*)
lemma mod_4_k4_3n:
  fixes n k :: nat
  assumes "odd k \<and> odd n" 
  shows "int (k^4 + n^2) mod 4 = 2"
  using assms by (smt (verit, best) add_cancel_right_right int_ops(2) int_ops(3) linorder_neqE_nat mod_4_k mod_4_n mod_add_eq mod_less not_add_less2 numeral_Bit0 numeral_One one_add_one zmod_int)

(* Sledece 3 pomocne leme i cetvrta glavna nam daju dokaz da je 7^k mod 4 = 3 *)
lemma help_y_mod_4:
  fixes y::int
  shows "(4*y + 3) mod 4 = 3"
  by simp

lemma help_y_49:
  fixes y::int
  assumes "y mod 4 = 3"
  shows "49*y mod 4 = 3"
  by (metis add.commute add.right_neutral assms mod_mod_trivial mod_mult_cong mod_mult_self1_is_0 mult_2 mult_numeral_1 numeral_Bit0 numeral_One zmod_numeral_Bit1)

lemma help_dvd_4:
  fixes x::nat
  shows "4 dvd (7*((49::int)^x) - 3)"
proof(induct x)
  case 0
  thus ?case 
    by auto
next 
  case(Suc x)
  have "(7*((49::int)^x) - 3) mod 4 = 0" using Suc by presburger
  then have "(7*((49::int)^x) mod 4 - 3 mod 4) mod 4 = 0" by (metis mod_diff_eq)
  then have "7*((49::int)^x) mod 4 = 3" by (auto simp add:algebra_simps) 
  then have "\<exists> y. 4*y+3 = 7*((49::int)^x)" by (metis Suc diff_add_cancel dvdE)
  then obtain y where "4*y+3 = 7*((49::int)^x)" by auto
  have "(7*((49::int)^(Suc x)) - 3) = 7*(((49::int)^x) * 49) - 3" by simp
  also have "\<dots> = 49*(4*y + 3) - 3" using \<open>(4::int) * (y::int) + (3::int) = (7::int) * (49::int) ^ (x::nat)\<close> by presburger
  have "(49*(4*y + 3) - 3) mod 4 = (49*(4*y + 3) mod 4 - 3 mod 4) mod 4" by (metis mod_diff_eq)
  then have "\<dots> = 0" by (metis help_y_mod_4 help_y_49 eq_iff_diff_eq_0 mod_0 mod_diff_right_eq)
  then show ?case by (metis \<open>((49::int) * ((4::int) * (y::int) + (3::int)) - (3::int)) mod (4::int) = ((49::int) * ((4::int) * y + (3::int)) mod (4::int) - (3::int) mod (4::int)) mod (4::int)\<close> \<open>(7::int) * ((49::int) ^ (x::nat) * (49::int)) - (3::int) = (49::int) * ((4::int) * (y::int) + (3::int)) - (3::int)\<close> calculation dvd_eq_mod_eq_0)
qed

lemma mod_4_7k:
  fixes k::nat
  assumes"odd k"
  shows"(7::int)^k mod 4 = 3"
  using assms
proof-
  have "7*(49::int)^x mod 4 = 3" by (metis add.commute help_y_mod_4 help_dvd_4 mod_eq_dvd_iff mod_mult_self2)
  have "\<exists>x. k = 2*x + 1" using assms by (meson oddE)
  then obtain x where "k = 2*x + 1" by auto
  then have "(7::int)^k = 7^(2*x + 1)" by auto
  then have "\<dots> = 7*7^(2*x)" by simp
  then have "\<dots> = 7*(7^2)^x"  by (simp add: power_mult)
  then have "\<dots> = 7*49^x" by auto
  then show ?thesis  by (metis \<open>(7::int) ^ (k::nat) = (7::int) ^ ((2::nat) * (x::nat) + (1::nat))\<close> add.commute help_y_mod_4 help_dvd_4 mod_eq_dvd_iff mod_mult_self2 mult.left_neutral mult_Suc_right power.simps(2) power_mult)
qed

(*Dokaz da je 3^n mod 4 = 3*)
lemma mod_4_3n:
  fixes n::nat
  assumes"odd n"
  shows"(3::int)^n mod 4 = 3"
  using assms
  by (metis mod_4_7k odd_one power_mod power_one_right)

(*Sada posto je (k^4 + n^2) mod 4 = 2, a (7^k - 3^n) mod 4 = 0, imamo kontradikciju
  i zakljucujemo da su k i n oba parni *)
lemma even_k_n:
  fixes n k :: nat
  assumes "7^k - 3^n dvd int(k^4 + n^2)"
  shows "even k \<and> even n"
  unfolding same_parity mod_4_k4_3n mod_4_7k mod_4_3n
proof(rule ccontr)
  assume "\<not>(even k \<and> even n)"
  from this have "odd k \<and> odd n" using assms even_k4_n2 same_parity by blast 
  then have "int (k^4 + n^2) mod 4 = 2" using mod_4_k4_3n by auto
  have "((7^k - 3^n)::int) mod 4 = ((7^k mod 4 - 3^n mod 4)::int) mod 4" by (auto simp add:mod_diff_eq)
  also have "\<dots> = 0" using `odd k \<and> odd n` by (simp add: mod_4_3n mod_4_7k)
  then have "((7^k - 3^n)::int) mod 4 = 0" using `((7^k - 3^n)::int) mod 4 = ((7^k mod 4 - 3^n mod 4)::int) mod 4` by auto
  then show False using assms `int(k^4 + n^2) mod 4 = 2` by auto
qed

(* Naredne 3 leme nam pomazu da dokazemo glavnu nejednakost koju cemo koristiti
  kasnije u dokazu. Posto su k i n parni, mozemo ih zapisati kao 2*a i 2*b 
  za neko a i b iz nat, pa na dalje dokazujemo 
  7^a + 3^b \<le> 8*a^4 + 2*b^2
*)
lemma help_dvd:
  fixes a b c::nat
  assumes"2*a dvd 2*b"
  shows"a dvd b"
  using assms
  by simp

lemma help_inequality_dvd:
  fixes a b ::nat
  assumes"a dvd b""a > 0" "b > 0"
  shows "a \<le> b"
  using assms
  by(auto simp add:Nat.dvd_imp_le)

lemma help_2times_dvd:
  fixes a b c::int
  assumes "a*2*b=c"
  shows "2*b dvd c"
  using assms by force

lemma main_inequality:
  fixes a b k n::nat
  assumes "k>0 \<and> n>0" "k = a*2" "n = b*2" "7^k - 3^n dvd int(k^4 + n^2)"
  shows"7^a + 3^b \<le> 8*a^4 + 2*b^2"
proof-
  have "(7::int)^k - 3^n = 7^(a*2) - 3^(b*2)" using assms by auto
  then have "7^(a*2) - 3^(b*2) = int((7^a)^2) - (3^b)^2" by(auto simp add:Power.monoid_mult_class.power_mult)
  also have "\<dots> = (7^a + 3^b)*(7^a - 3^b)" by(auto simp add:Power.monoid_mult_class.power2_eq_square Rings.comm_ring_class.square_diff_square_factored)
  also have "\<dots> = ((7^a - 3^b)/2) * 2 * ((7::int)^a + 3^b)" by simp
  then have "2*((7::int)^a + 3^b) dvd 7^k - 3^n" by (metis assms(2) assms(3) help_2times_dvd calculation dvd_div_mult_self even_7k_3n int_diff_cases mult_of_int_commute of_int_diff of_int_of_nat_eq) 
  have "int(k^4 + n^2) = 2*(8*a^4 + 2*b^2)"using assms(2) assms(3) by fastforce
  then have "2*((7::nat)^a + 3^b) dvd 2*(8*a^4 + 2*b^2)" by (smt (verit, ccfv_threshold) \<open>(2::int) * ((7::int) ^ (a::nat) + (3::int) ^ (b::nat)) dvd (7::int) ^ (k::nat) - (3::int) ^ (n::nat)\<close> assms(4) dvd_trans int_dvd_int_iff int_ops(5) mult_2 numeral_Bit1 numeral_One of_nat_numeral of_nat_power)
  then have "((7::nat)^a + 3^b) dvd (8*a^4 + 2*b^2)" using help_dvd by blast
  have "((7::nat)^a + 3^b) > 0"  by auto
  have "(8*a^4 + 2*b^2) > 0" using assms(1) assms(3) by auto
  then show "7^a + 3^b \<le> 8*a^4 + 2*b^2" using `((7::nat)^a + 3^b) dvd (8*a^4 + 2*b^2)` `((7::nat)^a + 3^b) > 0` `(8*a^4 + 2*b^2) > 0` help_inequality_dvd by auto
qed

(* Narednih 5 manjih lema nam pomazu da dokazemo nejednakost
  8*a^4 < 7^a
  *)
lemma help_a:
  fixes a::nat
  assumes "a \<noteq> 0"
  shows"8*(a+1)^4 = 8*a^4*((a+1)/a)^4"
  by (simp add: assms power_divide)

lemma help_mult_both_sides:
  fixes a::real
  fixes b::real
  assumes"a > b" "c > 1" 
  shows"a*c > b*c"
  using assms(1) assms(2) by auto

lemma help_1_a:
  fixes a::nat
  assumes "a\<ge>4"
  shows"1 + 1/a \<le> 1 + 1/4"
  using assms by force

lemma help_a_1_a_5_4:
  fixes a::nat
  assumes "a\<ge>4"
  shows"(a+1)/a \<le> 5/4"
proof-
  have "a\<noteq>0" using assms by auto
  then have "1 + 1/a = (a+1)/a" by (simp add: add_divide_distrib)
  then show "(a+1)/a \<le> 5/4" by (metis (no_types, opaque_lifting) add_divide_distrib assms help_1_a div_self numeral_Bit0 numeral_Bit1 zero_neq_numeral)
qed

lemma help_numbers:
  fixes a b::real
  shows"((5::real)/4)^4 = 625/256"
  by(auto simp add: Power.field_class.power_divide)

lemma inequality_8a4_7a:
  fixes a::nat
  assumes "a \<ge> 4"
  shows"8*a^4 < 7^a"
  using assms
proof(induction a rule:nat_induct_at_least)
  case base
  show ?case by simp
next
  case(Suc a)
  have "a \<noteq> 0" using Suc(1) by auto
  have "((a+1)/a) > 1"  using `a \<noteq> 0` by force
  then have "((a+1)/a)^4 > 1" by force
  have "(7::real)^a > 1" using `a \<noteq> 0` by auto
  have "real(8*a^4) < real(7^a)"using Suc.IH by linarith
  have "8*(Suc a)^4 = (8*a^4)*(((a+1)/a)^4)" using Suc_eq_plus1 \<open>(a::nat) \<noteq> (0::nat)\<close> help_a by presburger 
  also have "\<dots> < (7::real)^a*(((a+1)/a)^4)" using Suc `((a+1)/a)^4 > 1` using \<open>real ((8::nat) * (a::nat) ^ (4::nat)) < real ((7::nat) ^ a)\<close> by force
  also have "\<dots> \<le> (7::real)^a*(((5::real)/4)^4)" using Suc.hyps help_a_1_a_5_4 by force
  also have "\<dots> = (7::real)^a*((625::real)/256)" using help_numbers by presburger
  also have "\<dots> < (7::real)^a*7" by simp
  also have "\<dots> = 7^(Suc a)" by simp
  finally show ?case using of_nat_less_numeral_power_cancel_iff by blast
qed

(* Sledeca lema nam pomaze da dokazemo nejednakost
    2*b^2 < 3^b
*)
lemma help_4b_2_23b:
  fixes b::nat
  assumes "b\<ge>1"
  shows"4*b + 2 \<le> 2*3^b"
  using assms
proof(induction b rule:nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc b)
  have"2*(2*Suc b + 1) = 4*b + 2 + 4" by auto
  also have "\<dots> \<le> 2*3^b + 4" using Suc by auto
  also have "\<dots> \<le> 6*3^b" by auto
  finally show ?case by auto
qed

lemma inequality_2b2_3b:
  fixes b::nat
  assumes"b\<ge>1"
  shows"2*b^2 < 3^b"
  using assms
proof(induction b rule: nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc b)
  have "2*(Suc b)^2 = 2*b^2 + 4*b + 2" by (auto simp add:power2_eq_square)
  also have "\<dots> < 3^b + 4*b + 2" using Suc by auto
  also have "\<dots> \<le> 3^b + 2*3^b" using help_4b_2_23b `b \<ge> 1` by auto
  also have "\<dots> = 3^(b + 1)" by auto
  finally show ?case by auto
qed

(* Sledeca lema nam pomaze da dokazemo nejednakost
    2*b^2 + 1 < 3^b
*)
lemma help_4b_3_23b:
  fixes b::nat
  assumes "b\<ge>3"
  shows"4*b + 3 \<le> 2*3^b"
  using assms
proof(induction b rule:nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc b)
  have"2*(2*Suc b) + 3 = 4*b + 3 + 4" by auto
  also have "\<dots> \<le> 2*3^b + 4" using Suc by auto
  also have "\<dots> \<le> 6*3^b" by auto
  finally show ?case by auto
qed

lemma inequality_2b2_1_3b:
  fixes b::nat
  assumes"b\<ge>3"
  shows"2*b^2 + 1 < 3^b"
  using assms
proof(induction b rule: nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc b)
  have "2*(Suc b)^2 + 1 = 2*b^2 + 4*b + 3" by (auto simp add:power2_eq_square)
  also have "\<dots> < 3^b + 4*b + 3" using Suc by auto
  also have "\<dots> \<le> 3^b + 2*3^b" using help_4b_3_23b `b \<ge> 3` by auto
  also have "\<dots> = 3^(b + 1)" by auto
  finally show ?case by auto
qed

(* Pomocna lema za razliku kvadrata koja se koristi u glavnom dokazu *)
lemma help_diff_of_squares_abs:  
  fixes a b:: int
  assumes "a > 0" "b > 0"
  shows "abs(a^2 - b^2) = abs(a - b)*abs(a+b)" 
  by (simp add: abs_mult power2_eq_square square_diff_square_factored)

(* Pomocna lema za induktivni deo dokaza
  abs(49 - 3^b) \<ge> 22
*)
lemma help_49_3b_neg:
  fixes b::nat
  assumes "b \<ge> 4"
  shows "49 - (3::int)^b < 0"
  using assms
proof(induction b rule: nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc n)
  have "49 - (3::int)^(Suc b) = 49 - 3*3^b" by auto
  also have "\<dots> = 49 - 3^b - 2*3^b" by auto
  then show ?case by (smt (verit, del_insts) Suc(2) dvd_triv_left power_Suc2 zdvd_imp_le zero_less_power)
qed

(* Dokaz za abs(49 - (3::int)^b) \<ge> 22.
  Dokaz je malo duzi zbog primene indukcije tek za b \<ge> 4.
  Moguce je da postoji krace resenje, ali ga nisam nasao *)
lemma help_abs_22:  
  fixes b::nat
  assumes "b > 0"
  shows"abs(49 - (3::int)^b) \<ge> 22"
proof(cases)
  assume"b = 1"
  then show ?thesis
    by auto
next
  assume"\<not>(b = 1)"
  then have "b > 1" using assms by auto
  then show ?thesis 
  proof (cases)
    assume "b = 2"
    then show ?thesis by auto
  next 
    assume "\<not>(b = 2)"
    then have "b > 2" using `b > 1` by auto
    then show ?thesis 
    proof(cases)
      assume "b = 3"
      then show ?thesis by auto
    next
      assume "\<not>(b = 3)"
      then have "b \<ge> 4" using `b > 2` by auto
      then show ?thesis 
      proof(induction b rule: nat_induct_at_least)
        case base
        then show ?case by auto
      next
        case (Suc n)
        have "abs(49 - (3::int)^(Suc b)) = abs(49 - 3*(3::int)^b)" by auto
        also have "\<dots> = abs(49 - 3^b - 2*3^b)" by auto
        also have "\<dots> = abs(49 - 3^b) + 2*3^b" using `b \<ge> 4` using help_49_3b_neg by fastforce
        then show ?case by (smt (verit, best) Suc(1) Suc(2) help_49_3b_neg dvd_triv_left power_Suc2 zdvd_imp_le)
      qed 
    qed
  qed
qed

(* Sledeca lema i dokaz posle nje se svode na slicne korake kao dokaz pre, 
  na kraju dobijamo da je abs(343 - 3^b) \<ge> 100 *)
lemma help_343_3b_neg:
  fixes b::nat
  assumes "b \<ge> 6"
  shows "343 - (3::int)^b < 0"
  using assms
proof(induction b rule: nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc n)
  have "343 - (3::int)^(Suc b) = 343 - 3*3^b" by auto
  also have "\<dots> = 343 - 3^b - 2*3^b" by auto
  then show ?case by (smt (verit, del_insts) Suc(2) dvd_triv_left power_Suc2 zdvd_imp_le zero_less_power)
qed

lemma help_abs_343:  
  fixes b::nat
  assumes "b > 0"
  shows"abs(343 - (3::int)^b) \<ge> 100"
proof(cases)
  assume"b = 1"
  then show ?thesis
    by auto
next
  assume"\<not>(b = 1)"
  then have "b > 1" using assms by auto
  then show ?thesis 
  proof (cases)
    assume "b = 2"
    then show ?thesis by auto
  next 
    assume "\<not>(b = 2)"
    then have "b > 2" using `b > 1` by auto
    then show ?thesis 
    proof(cases)
      assume "b = 3"
      then show ?thesis by auto
    next
      assume "\<not>(b = 3)"
      then have "b > 3" using `b > 2` by auto
      then show ?thesis 
      proof(cases)
          assume "b = 4"
          then show ?thesis by auto
      next
          assume "\<not>(b = 4)"
          then have "b > 4" using `b > 3` by auto
          then show ?thesis
          proof(cases)
            assume "b = 5"
            then show ?thesis by auto
          next
            assume "\<not>(b = 5)"
            then have "b \<ge> 6" using `b > 4` by auto
            then show ?thesis
            proof(induction b rule:nat_induct_at_least)
              case base
              then show ?case by auto
            next
              case (Suc n)
              have "abs(343 - (3::int)^(Suc b)) = abs(343 - 3*(3::int)^b)" by auto
              also have "\<dots> = abs(343 - 3^b - 2*3^b)" by auto
              also have "\<dots> = abs(343 - 3^b) + 2*3^b" using `b \<ge> 6` using help_343_3b_neg by fastforce
              then show ?case by (smt (verit, best) Suc(1) Suc(2) help_343_3b_neg dvd_triv_left power_Suc2 zdvd_imp_le)
            qed
          qed
        qed
     qed
  qed
qed

(* Konacno, imamo dokaz glavnog tvrdjenja.
  Dokaz se svodi na dokaz po slucajevima gde najpre eliminisemo
  sve slucajeve za a \<ge> 4, a zatim redom dolazimo do resenja za
  a = 1, b = 2, tj. k = 2, n = 4 i dolazimo do kontradikcije 
  za a = 2 i a = 3 pomocu prethodna dva dokaza sa apsolutnim vrednostima *)

lemma main_task:
  fixes n k :: nat
  assumes "k>0 \<and> n>0" "7^k - 3^n dvd int(k^4 + n^2)"
  shows "k = 2 \<and> n = 4"
  using assms
proof-
  have "even k \<and> even n" using even_k_n `7^k - 3^n dvd int(k^4 + n^2)` by auto
  then have "\<exists> a b. 2*a = k \<and> 2*b = n" by auto
  then obtain a b where "2*a = k \<and> 2*b = n" by auto
  then have "b \<ge> 1" using `k>0 \<and> n>0` by auto
  have "k = a*2" using `2*a = k \<and> 2*b = n` by auto
  have "n = b*2" using `2*a = k \<and> 2*b = n` by auto
  then show ?thesis using `2*a = k \<and> 2*b = n`
  proof(cases)
    assume "a \<ge> 4"
    then show ?thesis
    proof-
      have "8*a^4 < 7^a" using `a \<ge> 4` inequality_8a4_7a by auto
      have "2*b^2 < 3^b" using `b \<ge> 1` inequality_2b2_3b by auto
      then have "8*a^4 + 2*b^2 < 7^a + 3^b" using `8*a^4 < 7^a` by auto
      have "7^a + 3^b \<le> 8*a^4 + 2*b^2" using `k>0 \<and> n>0` `k = a*2` `n = b*2` `7^k - 3^n dvd int(k^4 + n^2)` main_inequality by auto
      then have False using `8*a^4 + 2*b^2 < 7^a + 3^b` by auto
      then show ?thesis by auto
    qed
  next
    assume "\<not>(a \<ge> 4)"
    then have "a < 4" by auto
    have "a \<noteq> 0" using `k>0 \<and> n>0``2*a = k \<and> 2*b = n` by auto
    then have "a = 1 \<or> a = 2 \<or> a = 3" using `a < 4` by auto
    then show ?thesis
    proof
      assume"a = 1"
      then show ?thesis
      proof-
        have "k = 2" using `2*a = k \<and> 2*b = n` `a = 1` by auto
        have "7^a + 3^b \<le> 8*a^4 + 2*b^2" using `k>0 \<and> n>0` `k = a*2` `n = b*2` `7^k - 3^n dvd int(k^4 + n^2)` main_inequality by auto
        then have "7 + 3^b \<le> 8 + 2*b^2" using `a = 1` by auto
        then have "2*b^2 + 1 \<ge> 3^b" by auto
        then show ?thesis
        proof(cases)
          assume"b \<ge> 3"
          then have "2*b^2 + 1 < 3^b" using inequality_2b2_1_3b by auto
          then have False using `2*b^2 + 1 \<ge> 3^b` by auto
          then show ?thesis by auto
        next
          assume "\<not>(b \<ge> 3)"
          then have "b < 3" by auto
          have "b \<noteq> 0" using `k>0 \<and> n>0``2*a = k \<and> 2*b = n` by auto
          then have "b = 1 \<or> b = 2" using `b < 3` by auto
          then show ?thesis
          proof
            assume"b = 1"
            then have "n = 2" using `2*a = k \<and> 2*b = n` by auto
            then have "7^k - 3^n = 2*(int(k^4 + n^2))" using `k=2` by auto
            then have False using `7^k - 3^n dvd int(k^4 + n^2)` using `k=2` `n=2` by auto
            then show ?thesis by auto
          next
            assume"b = 2" 
            then have "n = 4" using `2*a = k \<and> 2*b = n` by auto
            then show ?thesis using `k = 2` by auto
          qed
        qed
      qed
    next
      assume "a = 2 \<or> a = 3"
      then show ?thesis 
      proof
        assume "a = 2"
        have "b > 0" using `2*a = k \<and> 2*b = n` `k > 0 \<and> n > 0` by auto
        then have "b\<ge>1" by auto
        have "49 + (3::int)^b > 0" by (simp add: add_pos_pos)
        have "int(k^4 + n^2) > 0" using `k>0 \<and> n>0` by (meson add_gr_0 of_nat_0_less_iff zero_less_power)
        then have "k = 4" using `2*a = k \<and> 2*b = n` `a=2` by auto
        then have "int(k^4 + n^2) = 256 + 4*b^2" using `2*a = k \<and> 2*b = n` by auto
        also have "\<dots> \<ge> abs(7^4 - 3^n)" using `k = 4` `7^k - 3^n dvd int(k^4 + n^2)` `2*a = k \<and> 2*b = n``int(k^4 + n^2) > 0`  using calculation zdvd_imp_le by auto
        also have "abs(7^4 - 3^n) = abs((((7::int)^2)^2) - (3::int)^(2*b))" using `2*a = k \<and> 2*b = n` by auto
        also have "\<dots> = abs((((7::int)^2)^2) - (3^b)^2)" using `b > 0` by (auto simp add: Power.monoid_mult_class.power_even_eq)
        also have "\<dots> = abs(49^2 - (3^b)^2)" by auto
        also have "\<dots> = abs(49 - 3^b)*abs(49 + 3^b)" using help_diff_of_squares_abs zero_less_numeral zero_less_power by blast
        also have "\<dots> = abs(49 - (3::int)^b)*(49+(3::int)^b)" by auto
        also have "\<dots> \<ge> 22*(49+(3::int)^b)" using help_abs_22 `49 + (3::int)^b > 0`  by (meson `0 < b` less_le mult_le_cancel_right not_less)
        then have "256 + 4*b^2 \<ge> 22*(49+(3::int)^b)"using \<open>int ((k::nat) ^ (4::nat) + (n::nat)\<^sup>2) = int ((256::nat) + (4::nat) * (b::nat)\<^sup>2)\<close> calculation by auto
        then have "128 + 2*b^2 \<ge> 11*(49+(3::int)^b)" by auto
        then have "128 + 2*b^2 \<ge> 539 + 10*3^b + (3::int)^b" by (smt (verit, ccfv_SIG) int_ops(2) less_imp_of_nat_less numeral_Bit0 numeral_Bit1 numeral_One of_nat_add of_nat_power zero_le_power)
        then have False using inequality_2b2_3b `b \<ge> 1` by (smt (verit) numeral_Bit0 numeral_Bit1 numerals(1) of_nat_1 of_nat_add of_nat_power_less_of_nat_cancel_iff one_le_power)
        then show ?thesis by auto
      next 
        assume "a = 3"
        have "b > 0" using `2*a = k \<and> 2*b = n` `k > 0 \<and> n > 0` by auto
        have "343 + (3::int)^b > 0" by (simp add: add_pos_pos)
        have "int(k^4 + n^2) > 0" using `k>0 \<and> n>0` by (meson add_gr_0 of_nat_0_less_iff zero_less_power)
        then have "k = 6" using `2*a = k \<and> 2*b = n` `a=3` by auto
        then have "int(k^4 + n^2) = 1296 + 4*b^2" using `2*a = k \<and> 2*b = n` by auto
        also have "\<dots> \<ge> abs(7^6 - 3^n)" using `k = 6` `7^k - 3^n dvd int(k^4 + n^2)` `2*a = k \<and> 2*b = n``int(k^4 + n^2) > 0`  using calculation zdvd_imp_le by auto
        also have "abs(7^6 - 3^n) = abs((((7::int)^3)^2) - (3::int)^(2*b))" using `2*a = k \<and> 2*b = n` by auto
        also have "\<dots> = abs((((7::int)^3)^2) - (3^b)^2)" using `b > 0` by (auto simp add: Power.monoid_mult_class.power_even_eq)
        also have "\<dots> = abs(343^2 - (3^b)^2)" by auto
        also have "\<dots> = abs(343 - 3^b)*abs(343 + 3^b)" using help_diff_of_squares_abs zero_less_numeral zero_less_power by blast
        also have "\<dots> = abs(343 - (3::int)^b)*(343+(3::int)^b)" by auto
        also have "\<dots> \<ge> 100*(343+(3::int)^b)" using help_abs_343 `343 + (3::int)^b > 0`  by (meson `0 < b` less_le mult_le_cancel_right not_less)
        then have "1296 + 4*b^2 \<ge> 100*(49+(3::int)^b)"using `int(k^4 + n^2) = 1296 + 4*b^2` calculation by auto
        then have "648 + 2*b^2 \<ge> 50*(49+(3::int)^b)" by auto
        then have "648 + 2*b^2 \<ge> 2450 + 19*3^b + (3::int)^b" by (smt (verit, ccfv_SIG) int_ops(2) less_imp_of_nat_less numeral_Bit0 numeral_Bit1 numeral_One of_nat_add of_nat_power zero_le_power)
        then have False using inequality_2b2_3b `b \<ge> 1` by (smt (verit) numeral_Bit0 numeral_Bit1 numerals(1) of_nat_1 of_nat_add of_nat_power_less_of_nat_cancel_iff one_le_power)
        then show ?thesis by auto
      qed
    qed
  qed
qed



end