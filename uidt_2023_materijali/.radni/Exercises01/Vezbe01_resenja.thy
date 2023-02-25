
(*<*)
theory Vezbe01_resenja
  imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Primer jednostavne teorije]\<close>

text \<open>(a) Pokazati da važi komutativnost i asocijativnost 
          operacije @{text "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat"}.\<close>

lemma "(x::nat) + y = y + x"
  by simp

lemma "((x::nat) + y) + z = x + (y + z)"
  by simp

text \<open>(b) Definisati funkciju @{text "sledbenik :: nat \<Rightarrow> nat"} i 
          pokazati da važi @{text "sledbenik (sledbenik x) = x + 2"}.\<close>

definition sledbenik :: "nat \<Rightarrow> nat" where
  "sledbenik x = x + 1"

lemma "sledbenik (sledbenik x) = x + 2"
  unfolding sledbenik_def
  by simp

text \<open>(c) Pokazati da ako važi @{text "x > 0"} onda @{text "sledbenik x > 1"}.
          Te pokazati da ako važi @{text "x < 5"} onda @{text "sledbenik x < 6"}.\<close>

lemma "x > 0 \<longrightarrow> sledbenik x > 1"
  unfolding sledbenik_def
  by simp

lemma "x < 5 \<longrightarrow> sledbenik x < 6"
  unfolding sledbenik_def
  by simp

text \<open>(d) Prethodna dva tvrđenja uopštiti u opšte tvrđenje o ograničenosti sledbenika.\<close>

lemma ogranicenost_sledbenika:
  fixes a b :: nat
  assumes "a < x" "x < b"
  shows "a + 1 < sledbenik x \<and> sledbenik x < b + 1"
  unfolding sledbenik_def
  using assms
  by simp

text \<open>(e) Definisati funkciju @{text "kvadrat :: nat \<Rightarrow> nat"} i
          pokazati da važi @{text "kvadrat (x + 1) = kvadrat x + 2 * x + 1"}.\<close>

abbreviation kvadrat :: "nat \<Rightarrow> nat" where
  "kvadrat x \<equiv> x * x"

lemma "kvadrat (x + 1) = kvadrat x + 2 * x + 1"
  by simp

text \<open>(f) Definisati rekurzivnu funkciju @{text "sum :: nat list \<Rightarrow> nat"} koja računa sumu 
          liste prirodnih brojeva. Pokazati da se @{text "sum xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i 
          odgovarajuću početnu vrenodst akomulatora. Nako toga pokazati sledeće svojstvo 
          @{text "sum (xs @ ys) = sum xs + sum ys"}.\<close>

fun sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

lemma "sum xs = foldr (+) xs 0"
  by (induction xs) auto

lemma "sum (xs @ ys) = sum xs + sum ys"
  by (induction xs) auto

text \<open>(g) Definisati rekurzivnu funkciju @{text "len :: nat list \<Rightarrow> nat"} koja računa dužinu 
          liste prirodnih brojeva. Pokazati da se @{text "len xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i
          odgovarajuću početnu vrednost akumulatora (Savet: Zgodno je koristiti 
          lambda funkciju @{text "(\<lambda> x y. f x y)"} za definisanje funkcije koju prima
          @{text "foldr"}). Nako toga pokazati sledeće svojstvo 
          @{text "len (xs @ ys) = len xs + len ys"}.\<close>

fun len :: "nat list \<Rightarrow> nat" where
  "len [] = 0"
| "len (x # xs) = 1 + len xs"

lemma "len xs = foldr (\<lambda> x. (+) 1) xs 0"
  by (induction xs) auto

lemma "len (xs @ ys) = len xs + len ys"
  by (induction xs) auto

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Zapisivanje logičkih formula]\<close> 

text \<open>(a) Zapisati nekoliko logičkih formula koje uključuju 
          logičke konstante @{text "True"} i @{text "False"},
          logičke veznike @{text "\<not>"}, @{text "\<and>"}, @{text "\<or>"}, 
          @{text "\<longrightarrow>"}, i @{text "\<longleftrightarrow>"}/@{text "="}, i
          univerzalne i egzistencionalne kvantifikatore @{text "\<forall>"} i @{text "\<exists>"}\<close>

lemma "A \<and> B \<longrightarrow> A \<or> B"
  by simp

lemma "A \<and> A \<longleftrightarrow> A"
  by simp

lemma "A \<or> \<not> A \<longleftrightarrow> True"
  by simp

lemma "\<forall> x. P x \<longrightarrow> Q x"
  nitpick
  oops

lemma "(\<forall> x. P x \<longrightarrow> Q x) \<and> (\<exists> x. P x) \<longrightarrow> (\<exists> x. Q x)"
  sledgehammer
  by blast

text \<open>(b) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.\<close>

text \<open>(b.1) Ako onaj ko laže taj i krade i ako bar neko laže, onda neko i krade.\<close>

lemma "
    (\<forall> x. Laze x \<longrightarrow> Krade x) \<and>
    (\<exists> x. Laze x) \<longrightarrow>
    (\<exists> x. Krade x)"
  by auto

text \<open>(b.2) Ako ”ko radi taj ima ili troši” i ”ko ima taj peva” i ”ko troši taj peva”, onda
”ko radi taj peva”\<close>

lemma "
    (\<forall> x. Radi x \<longrightarrow> Ima x \<and> Trosi x) \<and>
    (\<forall> x. Ima x \<longrightarrow> Peva x) \<and>
    (\<forall> x. Trosi x \<longrightarrow> Peva x) \<longrightarrow>
    (\<forall> x. Radi x \<longrightarrow> Peva x)"
  by auto

text \<open>(c) Zapisati sledeći skup rečenica u logici prvog reda i dokazati njihovu 
          nezadovoljivost.\<close>

text \<open>(c.1) Ako je X prijatelj osobe Y, onda je i Y prijatelj osobe X.\<close>
text \<open>(c.2) Ako je X prijatelj osobe Y, onda X voli Y.\<close>
text \<open>(c.3) Ne postoji neko ko je povredio osobu koju voli.\<close>
text \<open>(c.4) Osoba Y je povredila svog prijatelja X.\<close>

lemma "
    (\<forall> x y. Prijetelj x y \<longrightarrow> Prijatelj y x) \<and>
    (\<forall> x y. Prijatelj x y \<longrightarrow> Voli x y) \<and>
    (\<not> (\<exists> x y. Voli x y \<and> Povredio x y)) \<and>
    (\<exists> y x. Prijatelj y x \<and> Povredio y x) \<longrightarrow>
    False"
  by auto

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
