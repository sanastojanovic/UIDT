
(*<*)
theory MyTheory
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Isar dokazi u logici prvog reda.]\<close>

lemma 
  assumes "(\<exists> x. P x)"
      and "(\<forall> x. P x \<longrightarrow> Q x)"
    shows "(\<exists> x. Q x)"
(*<*) oops (*>*)

lemma
  assumes "\<forall> c. Man c \<longrightarrow> Mortal c"
      and "\<forall> g. Greek g \<longrightarrow> Man g"
    shows "\<forall> a. Greek a \<longrightarrow> Mortal a"
(*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma
  assumes "\<forall> a. P a \<longrightarrow> Q a"
      and "\<forall> b. P b"
    shows "\<forall> x. Q x"
(*<*) oops (*>*)

lemma
  assumes "\<exists> x. A x \<or> B x"
    shows "(\<exists> x. A x) \<or> (\<exists> x. B x)"
(*<*) oops (*>*)

lemma
  assumes "\<forall> x. A x \<longrightarrow> \<not> B x"
    shows "\<not> (\<exists> x. A x \<and> B x)"
(*<*) oops (*>*)

text \<open>Formulisati i dokazati naredna tvrđenja u Isar jaziku:\<close>

text \<open>Ako za svaki broj koji nije paran važi da je neparan;\\
      i ako za svaki neparan broj važi da nije paran;\\
      pokazati da onda za svaki broj važi da je ili paran ili neparan.\<close>

text \<open>Ako svaki konj ima potkovice;\\
      i ako ne postoji čovek koji ima potkovice;\\
      i ako znamo da postoji makar jedan čovek;\\
      dokazati da postoji čovek koji nije konj.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Pravilo ccontr i classical.]\<close>

text \<open>Dokazati u Isar jeziku naredna tvrđenja pomoću pravila \<open>ccontr\<close>.\<close>

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
(*<*) oops (*>*)

text \<open>Dodatni primer:\<close>

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
(*<*) oops (*>*)

text \<open>Dokazati u Isar jeziku naredna tvrđenja pomoću pravila \<open>classical\<close>.\<close>

lemma "P \<or> \<not> P"
(*<*) oops (*>*)

text \<open>Dodatni primer:\<close>

lemma
  assumes "\<not> (\<forall> x. P x)"
    shows "\<exists> x. \<not> P x"
(*<*) oops (*>*)


text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Logčki lavirinti.]\<close>

text \<open>Svaka osoba daje potvrdan odgovor na pitanje: \<open>Da li si ti vitez?\<close>\<close>

lemma no_one_admits_knave:
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> ans)"
    shows ans
(*<*) oops (*>*)

text \<open>Abercrombie je sreo tri stanovnika, koje ćemo zvati A, B i C. 
      Pitao je A: Jesi li ti vitez ili podanik?
      On je odgovorio, ali tako nejasno da Abercrombie nije mogao shvati 
      što je rekao. 
      Zatim je upitao B: Šta je rekao? 
      B odgovori: Rekao je da je podanik.
      U tom trenutku, C se ubacio i rekao: Ne verujte u to; to je laž! 
      Je li C bio vitez ili podanik?\<close>

lemma Smullyan_1_1:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> ansA)"
      and "kB \<longleftrightarrow> \<not> ansA"
      and "kC \<longleftrightarrow> \<not> kB"
    shows kC
(*<*) oops (*>*)

text \<open>Abercrombie nije pitao A da li je on vitez ili podanik 
      (jer bi unapred znao koji će odgovor dobiti), 
      već je pitao A koliko od njih trojice su bili vitezovi. 
      Opet je A odgovorio nejasno, pa je Abercrombie upitao B što je A rekao. 
      B je tada rekao da je A rekao da su tačno njih dvojica podanici. 
      Tada je, kao i prije, C tvrdio da B laže. 
      Je li je sada moguće utvrditi da li je C vitez ili podanik?\<close>

definition exactly_two :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "exactly_two A B C \<longleftrightarrow> ((A \<and> B) \<or> (A \<and> C) \<or> (B \<and> C)) \<and> \<not> (A \<and> B \<and> C)"

lemma Smullyan_1_2:
  assumes "kB \<longleftrightarrow> (kA \<longleftrightarrow> exactly_two (\<not> kA) (\<not> kB) (\<not> kC))"
      and "kC \<longleftrightarrow> \<not> kB"
    shows "kC"
(*<*) oops (*>*)

text \<open>Abercrombie je sreo samo dva stanovnika A i B. 
      A je izjavio: Obojica smo podanici. 
      Da li možemo da zaključimo šta je A a šta je B?\<close>

lemma Smullyan_1_3:
  "x"
(*<*) oops (*>*)

text \<open>A nije rekao: Obojica smo podanici. 
      Ono što je on rekao je: Bar jedan od nas je podanik. 
      Ako je ova verzija odgovora tačna, šta su A i B?\<close>

lemma Smullyan_1_4:
  "x"
(*<*) oops (*>*)

text \<open>A je rekao: Svi smo istog tipa tj. 
      ili smo svi vitezovi ili podanici. 
      Ako je ova verzija priče tačna, 
      šta možemo zaključiti o A i B?\<close>

lemma Smullyan_1_5: 
  "x"
(*<*) oops (*>*)

text \<open>Primetiti da ova lema odgovara lemi \<open>no_one_admits_knave\<close>. 
      Zašto se ne može ništa zaključiti o osobi A?\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
