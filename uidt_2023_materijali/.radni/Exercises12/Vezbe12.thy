
(*<*)
theory Vezbe12
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=stek mašina.]\<close>

text \<open>Definisati algebarski tip podataka \<open>izraz\<close> koji predstavlja
      izraz koga čine konstante koje su prirodni brojevi, i tri
      binarne operacije plus, minus, i puta nad izrazom.\<close>

text \<open>Konstruisati proizvoljnu instancu tipa \<open>izraz\<close> i proveriti
      njenu ispravnost pomoću ključne reči \<open>term\<close>.\<close>

text \<open>Definisati funkciju \<open>vrednost :: izraz \<Rightarrow> nat\<close> koja računa
      vrednost izraza.\<close>

text \<open>Definisati izraze \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>, gde je
      $x_1 \equiv 2 + 3$, $x_2 \equiv 3 \cdot (5 - 2)$, i $x_3 \equiv 3 \cdot 4 \cdot (5 - 2)$.
      Izračunati vrednosti ovih izraza.\<close>

text \<open>Definisati tip \<open>stek\<close> kao listu prirodnih brojeva. 
      Dodavanje na vrh steka podrazumeva operaciju 
      \<open>Cons\<close> (dodavanje na početak liste).\<close>

text \<open>Definisati algebarski tip \<open>operacija\<close> koji predstavlja
      moguće operacije koje će se izvršavati nad stekom.
      Nad stekom je moguće primeniti operaciju za plus,
      minus, puta i dodavanje nogov elementa na stek.\<close>

text \<open>Definisati funkciju \<open>izvrsiOp :: operacija \<Rightarrow> stek \<Rightarrow> stek\<close> koja 
      izvršava datu operaciju nad stekom i vraća novo stanje steka.\<close>

text \<open>Definisati tip \<open>program\<close> kao listu operacija.\<close>

text \<open>Definisati funkciju \<open>prevedi :: izraz \<Rightarrow> program\<close> koja
      data izraz prevodi u listu operacija, tj. program.
      Primeniti ovu funkciju nad izrazima \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>.\<close>

text \<open>Definisati funkciju \<open>izvrsiProgram :: program \<Rightarrow> stek \<Rightarrow> stek\<close>
      koja primenjuje listu operacija, tj. program nad stekom.
      Izračunati vrednost ove funkcije kada se primeni nad
      programom (koji se dobiju prevođenjem izraza \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>)
      i praznim stekom.\<close>

text \<open>Dodatno, definisati funkciju \<open>racunar :: izraz \<Rightarrow> nat\<close> koja
      prevodi program izvršava program (koji se dobija prevođenjem izraza)
      nad praznim stekom. Takođe, testirati ovu funkciju nad izrazima
      \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>.\<close>

text \<open>Pokazati da računar korektno izračunava vrednost izraza, tj. da su
      funkcije \<open>racunar\<close> i \<open>vrednost\<close> ekvivalentne.
      \<open>Savet\<close>: Potrebno je definisati pomoćne leme generalizacijom.\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
