
(*<*)
theory Vezbe12_resenja
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=stek mašina.]\<close>

text \<open>Definisati algebarski tip podataka \<open>izraz\<close> koji predstavlja
      izraz koga čine konstante koje su prirodni brojevi, i tri
      binarne operacije plus, minus, i puta nad izrazom.\<close>

datatype izraz = 
    Const nat
  | Plus izraz izraz
  | Minus izraz izraz
  | Puta izraz izraz

text \<open>Konstruisati proizvoljnu instancu tipa \<open>izraz\<close> i proveriti
      njenu ispravnost pomoću ključne reči \<open>term\<close>.\<close>

term "Plus (Const 2) (Const 3)"

text \<open>Definisati funkciju \<open>vrednost :: izraz \<Rightarrow> nat\<close> koja računa
      vrednost izraza.\<close>

primrec vrednost :: "izraz \<Rightarrow> nat" where
  "vrednost (Const x) = x"
| "vrednost (Plus i1 i2) = vrednost i1 + vrednost i2"
| "vrednost (Minus i1 i2) = vrednost i1 - vrednost i2"
| "vrednost (Puta i1 i2) = vrednost i1 * vrednost i2"

text \<open>Definisati izraze \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>, gde je
      $x_1 \equiv 2 + 3$, $x_2 \equiv 3 \cdot (5 - 2)$, i $x_3 \equiv 3 \cdot 4 \cdot (5 - 2)$.
      Izračunati vrednosti ovih izraza.\<close>

definition x1 :: izraz where
  "x1 \<equiv> Plus (Const 2) (Const 3)"

definition x2 :: izraz where
  "x2 \<equiv> Puta (Const 3) (Minus (Const 5) (Const 2))"

definition x3 :: izraz where
  "x3 \<equiv> Puta (Plus (Const 3) (Const 4)) (Minus (Const 5) (Const 2))"

value "vrednost x1"
value "vrednost x2"
value "vrednost x3"

text \<open>Definisati tip \<open>stek\<close> kao listu prirodnih brojeva. 
      Dodavanje na vrh steka podrazumeva operaciju 
      \<open>Cons\<close> (dodavanje na početak liste).\<close>

type_synonym stek = "nat list"

text \<open>Definisati algebarski tip \<open>operacija\<close> koji predstavlja
      moguće operacije koje će se izvršavati nad stekom.
      Nad stekom je moguće primeniti operaciju za plus,
      minus, puta i dodavanje nogov elementa na stek.\<close>

datatype operacija = 
    OpPlus
  | OpMinus
  | OpPuta
  | OpPush nat

text \<open>Definisati funkciju \<open>izvrsiOp :: operacija \<Rightarrow> stek \<Rightarrow> stek\<close> koja 
      izvršava datu operaciju nad stekom i vraća novo stanje steka.\<close>

fun izvrsiOp :: "operacija \<Rightarrow> stek \<Rightarrow> stek" where
  "izvrsiOp (OpPush x) xs = x # xs"  
| "izvrsiOp OpPlus (a # b # xs) = (a + b) # xs"
| "izvrsiOp OpMinus (a # b # xs) = (a - b) # xs"
| "izvrsiOp OpPuta (a # b # xs) = (a * b) # xs"

text \<open>Definisati tip \<open>program\<close> kao listu operacija.\<close>

type_synonym program = "operacija list"

text \<open>Definisati funkciju \<open>prevedi :: izraz \<Rightarrow> program\<close> koja
      data izraz prevodi u listu operacija, tj. program.
      Primeniti ovu funkciju nad izrazima \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>.\<close>

primrec prevedi :: "izraz \<Rightarrow> program" where
  "prevedi (Const x) = [OpPush x]"
| "prevedi (Plus a b) = OpPlus # (prevedi a) @ (prevedi b)"
| "prevedi (Minus a b) = OpMinus # (prevedi a) @ (prevedi b)"
| "prevedi (Puta a b) = OpPuta # (prevedi a) @ (prevedi b)"

value x1
value "prevedi x1"
value x2
value "prevedi x2"
value x3
value "prevedi x3"

text \<open>Definisati funkciju \<open>izvrsiProgram :: program \<Rightarrow> stek \<Rightarrow> stek\<close>
      koja primenjuje listu operacija, tj. program nad stekom.
      Izračunati vrednost ove funkcije kada se primeni nad
      programe (koji se dobiju prevođenjem izraza \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>)
      i praznim stekom.\<close>

primrec izvrsiProgram :: "program \<Rightarrow> stek \<Rightarrow> stek" where
  "izvrsiProgram [] stek = stek" 
| "izvrsiProgram (op # program) stek = izvrsiOp op (izvrsiProgram program stek)"

value "prevedi x1"
value "izvrsiProgram (prevedi x1) []"
value "prevedi x2"
value "izvrsiProgram (prevedi x2) []"
value "prevedi x3"
value "izvrsiProgram (prevedi x3) []"

text \<open>Dodatno, definisati funkciju \<open>racunar :: izraz \<Rightarrow> nat\<close> koja
      prevodi program izvršava program (koji se dobija prevođenjem izraza)
      nad praznim stekom. Takođe, testirati ovu funkciju nad izrazima
      \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>.\<close>

definition racunar :: "izraz \<Rightarrow> nat" where
  "racunar x = hd (izvrsiProgram (prevedi x) [])"

value x1
value "racunar x1"
value x2
value "racunar x2"
value x3
value "racunar x3"

text \<open>Pokazati da računar korektno izračunava vrednost izraza, tj. da su
      funkcije \<open>racunar\<close> i \<open>vrednost\<close> ekvivalentne.
      \<open>Savet\<close>: Potrebno je definisati pomoćne leme generalizacijom.\<close>

lemma izvrsiprogram_append [simp]:
  shows "izvrsiProgram (p1 @ p2) s = izvrsiProgram p1 (izvrsiProgram p2 s)"
  by (induction p1) auto

lemma izvrsiprogram_prevedi [simp]:
  shows "izvrsiProgram (prevedi x) s = vrednost x # s"
  by (induction x arbitrary: s) auto

lemma hd_racunar_vrednost:
  shows "racunar x = vrednost x"
  unfolding racunar_def
  by auto

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
