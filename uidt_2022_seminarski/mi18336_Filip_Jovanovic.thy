theory mi18336_Filip_Jovanovic
  imports Complex_Main
begin 

text\<open>
https://imomath.com/srb/dodatne/nejedn_pripr2005_vb.pdf  (Zadatak 3)

Ako je     0 \<le> x,y,z \<le> 1     onda je     xy + yz + zx \<ge> 2xyz
\<close>

text \<open>Prvi deo seminarskog\<close>
lemma nejednakost3_postavka: 
  assumes "\<forall> x y z :: real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> 0 \<le> z \<and> z \<le> 1"
  shows "x*y + y*z + z*x \<ge> 2*x*y*z"
  sorry

text \<open>Drugi deo seminarskog\<close>
lemma nejednakost3_dokaz: 
  assumes "\<forall> x y z :: real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<and> 0 \<le> z \<and> z \<le> 1"
  shows "x*y + y*z + z*x \<ge> 2*x*y*z" 
proof-
  fix x y z :: real
  have "0 \<le> x*y  \<and>  x*y \<le> 1" by (simp add: assms)
  then have "0 \<le> y*z  \<and>  y*z \<le> 1" by (simp add: assms)
  then have "0 \<le> x*z  \<and>  x*z \<le> 1" by (simp add: assms)
  then have "x*y + y*z + x*z \<le> 3" by (smt (verit, del_insts) assms)
  then have "0 \<le> 2*x*y*z  \<and>  2*x*y*z \<le> 1" by (simp add: assms)
  then show ?thesis using assms by (smt (verit, del_insts))
qed




text \<open>
https://imomath.com/srb/dodatne/nejedn_pripr2005_vb.pdf  (Zadatak 4)

Ako su x, y, z pozitivni realni brojevi za koje je   x + y + z = 1   onda je   xy + yz + zx \<ge> 9xyz

Koriscenjem nejednakosti aritmeticke i geometrijske sredine dobijamo: 
xy + yz + zx = (xy + yz + zx) \<sqdot> 1 
             = (xy + yz + zx) \<sqdot> (x + y + z) 
             = x^2y + yz^2 + z^2x + xy2 + y^2z + zx^2 + 3xyz 
             \<ge> 2xyz + 2xyz + 2xyz + 3xyz = 9xyz.
\<close>

text \<open>Prvi deo seminarskog\<close>
lemma nejednakost4_postavka: 
  assumes "\<forall> x y z :: real. x + y + z = 1"
  shows "x*y + y*z + z*x \<ge> 9*x*y*z"
  sorry

text \<open>Drugi deo seminarskog\<close>
lemma nejednakost4_dokaz: 
  assumes "\<forall> x y z :: real. x + y + z = 1"
  shows "x*y + y*z + z*x \<ge> 9*x*y*z"
proof-
  fix x y z :: real
  have "x*y + y*z + z*x = (x*y + y*z + z*x) * 1" using assms by auto
  then have "(x*y + y*z + z*x) * 1 = (x*y + y*z + z*x) * (x + y + z)" using assms by auto
  then have "(x*y + y*z + z*x) * (x + y + z) = x^2*y + y*z^2 + z^2*x + x*y^2 + y^2*z + z*x^2 + 3*x*y*z" using assms by auto
  then have "x^2*y + y*z^2 + z^2*x + x*y^2 + y^2*z + z*x^2 + 3*x*y*z \<ge> 2*x*y*z + 2*x*y*z + 2*x*y*z + 3*x*y*z" by (metis assms le_numeral_extra(4))
  then have "2*x*y*z + 2*x*y*z + 2*x*y*z + 3*x*y*z = 9*x*y*z" by auto
  then show ?thesis using assms by (smt (verit, best))
qed




text \<open>
https://imomath.com/srb/dodatne/nejedn_pripr2005_vb.pdf  (Zadatak 6)

Neka su x, y i z  nenegativni brojevi takvi da je    x + y + z = 1.   Dokazati da je: xy + yz + 2zx \<le> 1/2

Kvadriranjem uslova    x + y + z = 1,  dobijamo da je   x^2 + y^2 + z^2 + 2xy + 2yz + 2zx = 1.
Odavde sledi da je    2(xy + yz + 2zx) = 1 - (x^2 + y^2 + z^2 - 2zx) 
                                       = 1 - (x - z)^2 - y^2
Jednakost vazi kada je x = z i y = 0, odnosno za x = z = 1/2 i y = 0.
\<close>

text \<open>Prvi deo seminarskog\<close>
lemma nejednakost6_postavka:
  assumes "\<forall> x y z. x \<ge> 0 \<and> y \<ge> 0 \<and> z \<ge> 0 \<and> x + y + z = 1"
  shows "x*y + y*z + 2*z*x \<le> 1/2"
  sorry

text \<open>Drugi deo seminarskog\<close>
lemma nejednakost6_dokaz:
  assumes "\<forall> x y z :: real. x \<ge> 0 \<and> y \<ge> 0 \<and> z \<ge> 0 \<and> x + y + z = 1"
  shows "x*y + y*z + 2*z*x \<le> 1/2"
proof-
  fix x y z :: real
  have "x^2 + y^2 + z^2 + 2*x*y + 2*y*z + 2*z*x = 1" using assms by blast
  then have "2*(x*y + y*z + 2*z*x) = 1 - (x^2 + y^2 + z^2 - 2*z*x)" by (smt (verit, ccfv_threshold) assms)
  then have "2*(x*y + y*z + 2*z*x) = 1 - (x - z)^2 - y^2" by (smt (verit, best) assms)
  then have "x = z \<and> y = 0" by (smt (verit, ccfv_threshold) assms)
  then have "x = 1/2 \<and> z = 1/2 \<and> y = 0"  by (smt (verit, del_insts) assms)
  then show ?thesis using assms by (smt (verit, ccfv_SIG))
qed




text \<open>
https://imomath.com/srb/zadaci/2014_opstinsko.pdf  (Treci razred B kategorija 4. zadatak)

Odrediti sve realne brojeve x \<ge> y \<ge> 1 za koje vazi: 2x^2 − xy − 5x + y + 4 = 0

Resenje: (x, y) = (2, 2)

Dokaz:
Brojevi x i x − y su nenegativni (po uslovu zadatka), pa vazi:
        x^2 − xy = x(x − y)   \<ge>   1 \<sqdot> (x − y) = x − y.  (da bi dole uklonili y,  "x^2 - xy" -> "x - y")
        x^2 - xy   \<ge>   x - y
Sada je
        0 = 2x^2 − xy − 5x + y + 4 
          = x^2 + x^2 − xy − 5x + y + 4
          = x^2 + x - y - 5x + y + 4   \<ge>   x^2 − 4x + 4 = (x − 2)^2
                                
Pa je x = 2. Zamenom u polaznu jednacinu dobijamo y = 2.
Jedino resenje jednacine je par (x, y) = (2, 2).
\<close>

text \<open>Prvi deo seminarskog\<close>
lemma jednakost3B4_postavka:
  assumes "\<forall> x y. x \<ge> y \<and> y \<ge> 1 \<and> 2*x^2 - x*y - 5*x + y + 4 = 0"
  shows "x = 2 \<and> y = 2"
  sorry

text \<open>Drugi deo seminarskog\<close>
lemma jednakost3B4_dokaz:
  assumes "\<forall> x y :: real. x \<ge> y \<and> y \<ge> 1 \<and> 2*x^2 - x*y - 5*x + y + 4 = 0"
  shows "x = 2 \<and> y = 2"
proof-
  fix x y :: real
  have "x \<ge> 0 \<and> x - y \<ge> 0" using assms by auto
  then have "x^2 - x*y = x*(x-y)" by (simp add: power2_eq_square right_diff_distrib')
  then have "0 = 2*x^2 - x*y - 5*x + y + 4" using assms by auto
  then have "2*x^2 - x*y - 5*x + y + 4 \<ge> x^2 - 4*x + 4" by (simp add: assms)
  then have "x^2 - 4*x + 4 = (x - 2)^2" by (smt (verit, best) assms)
  then show ?thesis by (smt (verit, best) assms)
qed




text \<open>
https://imomath.com/srb/zadaci/bilten2018.pdf  (Cetvrti razred B kategorija 1. zadatak)

U skupu realnih brojeva resiti jednacinu: (x − 7)^3 + (x + 3)^3 = 278(x − 2).

Resenja: x = 2, x = -6, x = 10

Dokaz:
Na osnovu formule za zbir kubova a^3 + b^3 = (a + b)(a^2 − ab + b^2) mozemo faktorisati levu stranu
        (x − 7)^3 + (x + 3)^3 = 278(x − 2).
        (2x − 4)((x − 7)^2 − (x − 7)(x + 3) + (x + 3)^2) = 278(x − 2).
Jedno resenje je ocigledno x1 = 2. 
Ostala resenja dobijamo posle skracivanja obe strane sa 2(x − 2): na levoj strani tada ostaje 
        (x^2 − 14x + 49) − (x^12 − 4x − 21) + (x^2 + 6x + 9) = 139
        x^2 - 4x + 79 = 139
Resavanjem kvadratne jednacine dobijamo preostala dva resenja:

  x2/3 = (4 \<plusminus> (16 + 240)^(1/2))/2
  x2/3 = (4 \<plusminus> 16) / 2
  x2 = −6 i x3 = 10.
\<close>

text \<open>Prvi deo seminarskog\<close>
lemma jednakost4B1_postavka:
  assumes "\<forall> x :: real. (x-7)^3 + (x+3)^3 = 278*(x-2)"
  shows "x = 2 \<or> x = -6 \<or> x = 10"
  sorry

text \<open>Drugi deo seminarskog\<close>
lemma jednakost4B1_dokaz:
  assumes "\<forall> x :: real. (x-7)^3 + (x+3)^3 = 278*(x-2)"
  shows "x = 2 \<or> x = -6 \<or> x = 10"
proof-
  fix x :: real
  have "(2*x - 4) * ((x - 7)^2 - (x - 7) * (x + 3) + (x + 3)^2) = 278 * (x - 2)" by (smt (z3) assms jednakost4B1_postavka) (* x1 = 2 *)
  then have "(x^2 - 14*x + 49) - (x^2 - 4*x - 21) + (x^2 + 6*x + 9) = 139" by (smt (verit, ccfv_threshold) assms jednakost4B1_postavka)
  then have "x^2 - 4*x + 79 = 139" using assms by auto
  then have "x^2 - 4*x - 60 = 0" by (smt (z3) assms jednakost4B1_postavka) (* x2 = -6, x3 = 10 *)
  then show ?thesis by (simp add: assms jednakost4B1_postavka)
qed

end