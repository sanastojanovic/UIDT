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
