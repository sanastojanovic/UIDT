theory mi18472_Aleksandra_Radosavljevic
  imports Complex_Main
begin

text \<open>
  a b c d su realni brojevi takvi da vazi "a + b +c + d = 6"
   i "a^2 + b^2 +c^2 + d^2 =12"
 dokazati da vazi nejednakost 
 36 \<le> 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)\<le> 48
\<close>

lemma cetvrti_stepen_razlike:
fixes x y :: real
shows  "(x - y) ^ 4 = x ^ 4 - 4*x^3*y + 6*x^2*y^2 - 4*x*y^3+ y^4"
proof-
  have "(x-y)^4 = (x-y)^2 *(x-y)^2 "
    by auto
  also have "... = (x ^ 2 - 2*x*y +y^2) *  (x ^ 2 - 2*x*y +y^2)"
(*sledgehammer*)
 by (smt (verit) mult_eq_0_iff power2_diff square_diff_square_factored)
   also have "... = x ^ 4 - 2*x^2*x*y + x^2*y^2 - 2*x*y*x^2 + 2*x*y*2*x*y - 2*x*y*y^2+ y^2*x^2 - y^2*2*x*y + y^4"
     by (auto simp add: algebra_simps)
  also have "... = x ^ 4 - 2*x^3*y + x^2*y^2 - 2*x*y*x^2 + 4*x*y*x*y - 2*x*y^3+ y^2*x^2  - y^3*2*x +  y^4"
     by (simp add: power2_eq_square power3_eq_cube)
  also have "... =  x ^ 4 - 2*x^3*y + x^2*y^2 - 2*y*x^3 + 4*x^2*y^2 - 2*x*y^3 + y^2*x^2 - 2*y^3*x + y^4"
     by (auto simp add: power2_eq_square power3_eq_cube algebra_simps)
  also have "... = x^4  - 2*x^3*y + x^2*y^2 - 2*x^3*y  + 4*x^2*y^2 - 2*x*y^3+ y^2*x^2 - 2*x*y^3 + y^4"
    by auto
  finally show ?thesis
    by auto
qed

lemma prva_opservacija_dokaza:
  fixes a b c d :: real
  assumes "a + b + c + d = 6"
  assumes "a⇧2 + b⇧2 + c⇧2 + d⇧2 = 12"
  shows "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
proof -
  have "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) =
         4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 - a ^4 - b ^4  - c ^4 - d ^4 "
    by auto
  also have "... = -( a^4 + b^4  + c^4 + d^4) +  4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 "
    by auto
  also have
    "... = -((a-1) ^4 + 4*a^3 - 6*a^2 + 4*a -1 + b ^4  + c ^4 + d ^4) +  4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 "
    (*da bismo dobili ovu razliku (a-1)^4 dodajemo posebnu lemu koja definise tu razliku *)
    by (auto simp add : cetvrti_stepen_razlike)
  also have "... = -((a-1) ^4 + b ^4  + c ^4 + d ^4)  + 6*a^2 - 4*a +1 + 4*b^3 + 4*c^3 + 4*d^3 "
    by auto
  (*sada koristimo ovu lemu da bismo dobili i (b-1)^4,(c-1)^4 i (d-1)^4) *)
 also have "... = -((a-1) ^4 + (b-1) ^4+ 4*b^3 - 6*b^2 + 4*b -1  + c ^4 + d ^4)  + 6*a^2 - 4*a +1 + 4*b^3 + 4*c^3 + 4*d^3 "
    by (auto simp add: cetvrti_stepen_razlike)
 also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + 4*c^3 - 6*c^2 + 4*c -1   + d ^4)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 4*c^3 + 4*d^3"
   by (auto simp add :  cetvrti_stepen_razlike)
 also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4 +  4*d^3 - 6*d^2 + 4*d -1)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 6*c^2 - 4*c +1 + 4*d^3"
   by (auto simp add: cetvrti_stepen_razlike)
 also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 6*c^2 - 4*c +1 + 4*d^3 - 4*d^3 + 6*d^2 - 4*d +1"
     by auto
   also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 6*(a^2 + b^2 + c^2 + d ^ 2) - 4*(a + b + c +d) +4"
     by auto
  (*iz pretpostavki imamo da je  a^2 + b^2 + c^2 + d ^ 2 =12, a  a + b + c +d = 6 i to koristimo ovde*)
   also have " ... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 6*12 - 4*6  + 4"
     using assms
     by auto
   finally show ?thesis
     by auto
 qed

lemma pomocna_lema1:
  fixes x y z t :: real
  shows "(x^2 + y^2 + z^2 + t^2)^2 = x^4 + y^4 + z^4 + t^4 + 2*(x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*z^2 + y^2*t^2 + z^2*t^2)"
proof-
  have "(x^2 + y^2 + z^2 + t^2) ^ 2 =  (x^2 + y^2 + z^2 + t^2) * (x^2 + y^2 + z^2 + t^2)"
    by (simp add: power2_eq_square)
  also have "... = x^2*x^2 + x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*x^2 + y^2*y^2 + y^2*z^2 + y^2*t^2 +  z^2*x^2 + z^2*y^2 + z^2*z^2 + z^2*t^2 +  t^2*x^2 + t^2*y^2 + t^2*z^2 + t^2*t^2  "
    by (auto simp add: algebra_simps)
  also have "\<dots> =x^4 + y^4 + z^4 + t^4 + 2*(x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*z^2 + y^2*t^2 + z^2*t^2) "
    by (auto simp add: algebra_simps)
  then show ?thesis
    (*sledgehammer*)
    using calculation by presburger
qed


lemma pomocna_lema2:
fixes x y z t :: real 
  shows "((x^2 + y^2 + z^2 + t^2)/4)^2*4 = ((x^2 + y^2 + z^2 + t^2)^2)/4"
proof-
  have "((x^2 + y^2 + z^2 + t^2)/4)^2*4 =((x^2 + y^2 + z^2 + t^2)^2/(4*4))*4 "
    by (simp add: power2_eq_square)
  also have "... = ((x^2 + y^2 + z^2 + t^2)^2/16)*4"
    by auto
  also have "... = ((x^2 + y^2 + z^2 + t^2)^2)/4"
    by auto
  finally show ?thesis
    .
qed


lemma kvadrat_razlike_sa1:
  fixes x :: real
  shows "(x-1) ^ 2 = x ^ 2 - 2*x + 1"
proof-
  have "(x-1)^2 = (x-1)*(x-1)"
    by (simp add: power2_eq_square)
  also have "... = x*x - x - x +1"
    by (simp add: algebra_simps)
  also have "... = x^2 - 2*x + 1"
    by (simp add: power2_eq_square)
  finally show ?thesis
    by auto
qed

lemma zbir_kv_je_4:
fixes a b c d x y z t :: real
  assumes "a + b + c + d = 6" "a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 = 12"
          "x = a-1 \<and> y = b-1 \<and> z = c-1 \<and> t = d-1"
  shows"x^2 + y^2 + z^2 + t^2 = 4"
proof-
  have "x^2 + y^2 + z^2 + t^2 = (a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2"
    using assms(3)
    by auto
  also have "... =( a^2 - 2*a + 1) + (b^2 - 2*b + 1) + (c^2 - 2*c + 1) + (d^2 - 2*d + 1) "
    by (simp add: kvadrat_razlike_sa1)
  also have "... = a^2 + b^2 + c^2 + d^2 - 2* (a + b + c + d) +4"
    by auto
  also have "... = 12 - 2*6 + 4"
    using assms(1) assms(2)
    by auto
  also have "... = 4"
    by auto
  finally show ?thesis
    .
qed

lemma konacna:
  fixes a b c d :: real
  assumes "a + b + c + d = 6"
  assumes "a⇧2 + b⇧2 + c⇧2 + d⇧2 = 12"
  shows "36 ≤ 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
        and "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48"
  proof-
  show " 36 ≤ 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
  proof- 
    have o1: "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
      using prva_opservacija_dokaza assms
     by auto
   (*sada uvodimo  x = (a-1); y=(b-1); z=(c-1); t=(d-1)
    jer iz prve opservacije dobijamo da 
    treba dokazati  "x^4 + y^4 + z^4 + t^4 ≤ 16
    i "4 ≤x^4 +y^4 +z^4 +t^4"*)
    
      let ?x = "a-1" and ?y = "b-1" and ?z = "c-1" and ?t = "d-1"
      have " ?x^4 +?y^4 + ?z^4 + ?t^4 ≤ (?x^2 + ?y^2 + ?z^2 + ?t^2)^2"
        by (auto simp add: pomocna_lema1)
      then have o2: "?x^4 +?y^4 + ?z^4 + ?t^4 ≤ 16"
        using assms zbir_kv_je_4
        by auto
      (*Sada koristimo sve sto smo pokazali da dokazemo prvu observaciju do kraja*)
         have o3:"4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -(?x^4 + ?y^4 + ?z^4 + ?t^4) + 52"
      using assms o1 o2
      by auto
    have " -16 + 52 ≤ 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
      using  o2 o3
      by auto
    then have "36 ≤ 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
      by auto
    then show ?thesis
      .
  qed
  next
  show "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48"
  proof -
     have o1: "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
      using assms prva_opservacija_dokaza
      by auto
    let ?x = "a-1" and ?y = "b-1" and ?z = "c-1" and ?t = "d-1"
    have "((?x^2 + ?y^2 + ?z^2 + ?t^2)/4)^2*4  ≤ (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      by (simp add: power_mean_inequality)
    then have o3:"((?x^2 + ?y^2 + ?z^2 + ?t^2)^2)/4 ≤ (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      by (simp add: pomocna_lema2)
    have o4: "?x^2 + ?y^2 + ?z^2 + ?t^2 = 4"
      using assms
      using zbir_kv_je_4 by blast
    then have "16 /4 ≤  (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      using o3 o4
      by (auto simp add:  power2_eq_square)
    then have "4 ≤  (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      by auto
    (* vracanje u zapis sa promenljivim a b c d *)
    then have "4 ≤  (a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4"
      by auto
    then have " -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) ≤ -4"
      by auto
    (*namestamo rezultat 48*)
    then have " -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52 ≤ -4+52"
      by auto
    then have "-((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52 ≤ 48" 
      by auto
    then have "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48"
      (*iz prve opservacije dokaza imamo da je leva strana  
      4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)
      = "-((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52  *)
      using o1
      by auto
    then show ?thesis
      .
  qed
 qed

end
