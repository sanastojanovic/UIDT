theory mi16026_Stefan_Stefanovic
  imports Main
begin
typ nat
typ bool
text\<open>Dokazati da ne postoje prirodni brojevi x i y takvi da su
     x^2+y^2 i x^2+4*y^2 potpuni kvadrati.\<close>

text \<open>x^2 + y^2\<close>
fun jed1 :: "(nat \<times> nat) \<Rightarrow> nat" where
  "jed1 (x,y) = (x^2)+(y^2)"

text \<open>x^2 + 4* y^2\<close>
fun jed2 :: "(nat \<times> nat) \<Rightarrow> nat" where
  "jed2 (x,y) = (x^2)+4*(y^2)"

text \<open>da li je n kvadrat od m\<close>
fun kvadrat :: "(nat \<times> nat) \<Rightarrow> bool" where
  "kvadrat (m,n) = (m^2=n)"

text\<open>Da li postoji prirodan broj manji ili jednak k koji kad se kvadrira daje n?
     Potpun kvadrat podrazumeva da je kvadrat prirodnog broja, tako da je validno
     ispitati svaki prirodan broj manji od njega. Isabelle ima definisanu funkciju
     kvadrata tako da smatram da ne moram da navodim lemu da je kvadrat svakog
     prirodnog broja veceg od n takodje veci od n, tj nema poente obradjivati ovde.\<close>
primrec imakvadrat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "imakvadrat 0 n = kvadrat (0,n)" |
  "imakvadrat (Suc k) n = (kvadrat ((Suc k),n) \<or> imakvadrat k n)"

text \<open>vidi da li je n potpun kvadrat k za svako k od 0 do n-1, koristeci 
      gorenavedene funkcije\<close>
fun pk :: "nat \<Rightarrow> bool" where
  "pk n = imakvadrat (n-1) n"

text \<open>zadatak u pitanju. prirodne brojeve definisemo kao nat veci od nule,
      ovako mozemo koristiti sve unapred definisane lepote nat skupa\<close>
theorem zadatak:
  fixes x y m n :: nat
  assumes "x>0 \<and> y>0 \<and> m>0 \<and> n>0"
  shows "\<forall>xy.\<not>(\<exists>mn.(pk (jed1(x,y)) \<and> pk (jed2(x,y))))"
  sorry
end

text ‹2. SEMINARSKI
imamo tri prosta broja, p, q, r i pozitivan broj n, tako da su
(p+n)/qr (q+n)/pr i (r+n)/pq celi brojevi.
Dokazati da je p=q=r
›

text ‹Definisemo prost broj tako sto proverimo za sve brojeve od 2 do n-1 dal dele›
primrec ne_deli :: "nat ⇒ nat ⇒ bool" where
  "ne_deli 0 n = True" |
  "ne_deli (Suc k) n = (if (k dvd n ∧ k>1) then False else ne_deli k n)"
fun prost :: "nat ⇒ bool" where
  "prost n =(if n<2 then False else ne_deli n n)"
value "prost 5"
text ‹ako neki broj ima delioca sem 1 i samog sebe, nije prost›
lemma delinijeprost:
  fixes m n :: nat
  assumes "n>1" "m>1" "m<n" "m dvd n"
  shows "prost n = False" sorry
text‹
proof-
   have s1:"ne_deli (Suc m) n = False"
    using assms(2) assms(4) by auto
  also have s2:"ne_deli m n = False"
    by simp
qed
›

text ‹prost broj dele samo on ili jedan›
lemma jedanilion:
  fixes x y :: nat
  assumes "x>0" "prost y" "x dvd y"
  shows "x=1 ∨ x=y"
proof (cases "x=1")
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
  proof (cases "x≤y")
    case True
    then show ?thesis
    proof (cases "x<y")
      case True
      then show ?thesis
        by (metis assms(1) assms(2) assms(3) delinijeprost gr_implies_not_zero less_one linorder_neqE_nat)
    next
      case False
      then show ?thesis
        by (simp add: True nat_less_le) 
    qed
  next
    case False
    then show ?thesis
      using assms(2) assms(3) dvd_imp_le by force
  qed
qed
text ‹zadatak. bez umanjenja opstosti gledamo da je p>q>r›
lemma metropolis1:
  fixes p q r n :: nat
  assumes "prost p" "prost q" "prost r" "n>0" "q*r dvd p+n" "p*r dvd q+n" "p*q dvd r+n" "p≥q" "q≥r"
  shows "p=q ∧ p=r ∧ q=r"
proof-
  have p1:"p dvd q+n"
    by (meson assms(6) dvd_mult_left)
  have p2:"p dvd r+n"
    using assms(7) dvd_mult_left by blast 
  from p1 p2 assms(9) have p3:"p dvd q-r"
    by (metis diff_cancel2 dvd_diff_nat)  
  have npnjd:"0≤q-r ∧ q-r<q ∧ q≤p" by (metis (no_types) add.left_neutral add_diff_cancel_right' assms(4) assms(5) assms(8) assms(9) diff_diff_cancel diff_le_self dvdE le_antisym mult_eq_0_iff not_less)
  from this have j1:"q=r"
  proof
    have "q ≤ r"
      by (metis npnjd diff_is_0_eq diff_right_commute linorder_neqE_nat nat_dvd_not_less not_le p3 zero_diff)
    then show ?thesis
      by (meson assms(9) linorder_neqE_nat not_le)
  qed
  have q1:"q dvd p + n"
    using ‹q = r› assms(5) dvd_mult_right by blast
  have q2:"q dvd r + n"
    using ‹q = r› assms(6) dvd_mult_right by blast
  have q3:"q dvd p - r"
    by (metis diff_cancel2 dvd_diff_nat q1 q2)
  have q4:"q dvd p - q"
    using j1 q3 by blast
  have q5:"q dvd p"
    by (simp add: npnjd less_eq_dvd_minus q4) 
  have j2:"p=q"
    by (metis One_nat_def assms(1) assms(3) cancel_comm_monoid_add_class.diff_cancel j1 jedanilion lessI npnjd numerals(2) prost.simps q5)
  have j3:"q=r"
    by (simp add: j1)
  from this show ?thesis
    by (simp add: j2)
qed
end
