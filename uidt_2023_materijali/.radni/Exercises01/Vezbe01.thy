
(*<*)
theory Vezbe01
  imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Primer jednostavne teorije]\<close>

text \<open>(a) Pokazati da važi komutativnost i asocijativnost 
          operacije @{text "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat"}.\<close>

text \<open>(b) Definisati funkciju @{text "sledbenik :: nat \<Rightarrow> nat"} i 
          pokazati da važi @{text "sledbenik (sledbenik x) = x + 2"}.\<close>

text \<open>(c) Pokazati da ako važi @{text "x > 0"} onda @{text "sledbenik x > 1"}.
          Te pokazati da ako važi @{text "x < 5"} onda @{text "sledbenik x < 6"}.\<close>

text \<open>(d) Prethodna dva tvrđenja uopštiti u opšte tvrđenje o ograničenosti sledbenika.\<close>

text \<open>(e) Definisati funkciju @{text "kvadrat :: nat \<Rightarrow> nat"} i
          pokazati da važi @{text "kvadrat (x + 1) = kvadrat x + 2 * x + 1"}.\<close>

text \<open>(f) Definisati rekurzivnu funkciju @{text "sum :: nat list \<Rightarrow> nat"} koja računa sumu 
          liste prirodnih brojeva. Pokazati da se @{text "sum xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i 
          odgovarajuću početnu vrenodst akomulatora. Nako toga pokazati sledeće svojstvo 
          @{text "sum (xs @ ys) = sum xs + sum ys"}.\<close>

text \<open>(g) Definisati rekurzivnu funkciju @{text "len :: nat list \<Rightarrow> nat"} koja računa dužinu 
          liste prirodnih brojeva. Pokazati da se @{text "len xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i
          odgovarajuću početnu vrednost akumulatora (Savet: Zgodno je koristiti 
          lambda funkciju @{text "(\<lambda> x y. f x y)"} za definisanje funkcije koju prima
          @{text "foldr"}). Nako toga pokazati sledeće svojstvo 
          @{text "len (xs @ ys) = len xs + len ys"}.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Zapisivanje logičkih formula]\<close> 

text \<open>(a) Zapisati nekoliko logičkih formula koje uključuju 
          logičke konstante @{text "True"} i @{text "False"},
          logičke veznike @{text "\<not>"}, @{text "\<and>"}, @{text "\<or>"}, 
          @{text "\<longrightarrow>"}, i @{text "\<longleftrightarrow>"}/@{text "="}, i
          univerzalne i egzistencionalne kvantifikatore @{text "\<forall>"} i @{text "\<exists>"}\<close>

text \<open>(b) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.\<close>

text \<open>(b.1) Ako onaj ko laže taj i krade i ako bar neko laže, onda neko i krade.\<close>

text \<open>(b.2) Ako ”ko radi taj ima ili troši” i ”ko ima taj peva” i ”ko troši taj peva”, onda
”ko radi taj peva”\<close>

text \<open>(c) Zapisati sledeći skup rečenica u logici prvog reda i dokazati njihovu 
          nezadovoljivost.\<close>

text \<open>(c.1) Ako je X prijatelj osobe Y, onda je i Y prijatelj osobe X.\<close>
text \<open>(c.2) Ako je X prijatelj osobe Y, onda X voli Y.\<close>
text \<open>(c.3) Ne postoji neko ko je povredio osobu koju voli.\<close>
text \<open>(c.4) Osoba Y je povredila svog prijatelja X.\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
