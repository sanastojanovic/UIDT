
(*<*)
theory MyTheory
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Alternirajuća suma neparnih prirodnih brojeva]\<close>

text \<open>Pokazati da važi:\<close>

text_raw \<open>$$ - 1 + 3 - 5 + \ldots + (- 1)^n (2n - 1) = (- 1)^n n.$$\<close>

text \<open>Primitivnom rekurzijom definisati funkciju \<open>alternirajuca_suma :: "nat \<Rightarrow> int"\<close> 
      koja računa alternirajucu sumu neparnih brojeva od \<open>1\<close> do \<open>2n - 1\<close>, 
      tj. definisati funkciju koja računa levu stranu jednakosti.\<close>

primrec alternirajuca_suma :: "nat \<Rightarrow> int" where
  "alternirajuca_suma 0 = undefined"
| "alternirajuca_suma (Suc n) = undefined"

text \<open>Proveriti vrednost funkcije \<open>alternirajuca_suma\<close> za proizvoljan prirodni broj.\<close>

text \<open>Dokazati sledeću lemu induckijom koristeći metode za automatsko dokazivanje.\<close>

lemma "alternirajuca_suma n = (-1)^n * int n"
(*<*) oops (*>*)

text \<open>Dokazati sledeću lemu indukcijom raspisivanjem detaljnog Isar dokaza.\<close>

lemma "alternirajuca_suma n = (-1)^n * int n"
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Množenje matrica]\<close>

text \<open>Pokazati da važi sledeća jednakost:\<close>

text_raw 
\<open>$$
\begin{pmatrix}
1 & 1\\
0 & 1
\end{pmatrix}^n
=
\begin{pmatrix}
1 & n\\
0 & 1
\end{pmatrix},
n \in \mathbb{N}.
$$\<close>

text \<open>Definisati tip \<open>mat2\<close> koji predstavlja jednu \<open>2\<times>2\<close> matricu prirodnih brojeva.
      Tip \<open>mat2\<close> definisati kao skraćenicu uređene četvorke prirodnih brojeva.
      Uređena četvorka odgovara \<open>2\<times>2\<close> matrici kao\<close>

text_raw 
\<open>$$
(a, b, c, d) \equiv
\begin{pmatrix}
a & b\\
c & d
\end{pmatrix}.
$$\<close>

text \<open>Definisati konstantu \<open>eye :: mat2\<close>, koja predstavlja jediničnu matricu.\<close>

text \<open>Definisati funkciju \<open>mat_mul :: mat2 \<Rightarrow> mat2 \<Rightarrow> mat2\<close>, koja množi dve matrice.\<close>

fun mat_mul where
  "mat_mul (a1, b1, c1, d1) (a2, b2, c2, d2) = undefined"

text \<open>Definisati funkciju \<open>mat_pow :: mat2 \<Rightarrow> nat \<Rightarrow> mat2\<close>, koja stepenuje matricu.\<close>

fun mat_pow where
  "mat_pow _ _ = undefined"

text \<open>Dokazati sledeću lemu koristeći metode za automatsko dokazivanje.\<close>

lemma "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
(*<*) oops (*>*)

text \<open>Dokazati sledeću lemu indukcijom raspisivanjem detaljnog Isar dokaza.\<close>

lemma "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Deljivost]\<close>

text \<open>Pokazati sledeću lemu.\\
      \<open>Savet\<close>: Obrisati \<open>One_nat_def\<close> i \<open>algebra_simps\<close> iz \<open>simp\<close>-a u 
      finalnom koraku dokaza.\<close>

lemma 
  fixes n::nat
  shows "(6::nat) dvd n * (n + 1) * (2 * n + 1)"
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Nejednakost]\<close>

text \<open>Pokazati da za svaki prirodan broj \<open>n > 2\<close> važi \<open>n\<^sup>2 > 2 * n + 1\<close>.\\
     \<open>Savet\<close>: Iskoristiti \<open>nat_induct_at_least\<close> kao pravilo indukcije i 
              lemu \<open>power2_eq_square\<close>.\<close>

thm nat_induct_at_least
thm power2_eq_square

lemma n2_2n:
  fixes n::nat
  assumes "n \<ge> 3"
  shows "n\<^sup>2 > 2 * n + 1"
  using assms
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
