
(*<*)
theory Vezbe02
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Zapisivanje logičkih formula (nastavak)]\<close>

text \<open>(a) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.\<close>

text \<open>(a.1) Ako ”šta leti to ima krila i lagano je” 
            i ”šta pliva, to nema krila”, 
            onda ”šta pliva, to ne leti”\<close>

text \<open>(a.2) Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi, 
            onda za svaku nogu postoji cipela koja joj u nekom trenutku odgovara 
            i za svaku nogu postoji trenutak takav da postoji cipela koja joj u tom 
            trenutku odgovara.\<close>

text \<open>(b) Pokazati da je rečenica P logička posledica rečenica P1, P2, P3.\<close>

text \<open>P:  Andrija voli da pleše.\<close>
text \<open>P1: Svako ko je srećan voli da peva.\<close>
text \<open>P2: Svako ko voli da peva, voli da pleše.\<close>
text \<open>P3: Andrija je srećan.\<close>

text \<open>P':  Svako dete voli da se igra.\<close>
text \<open>P1': Svaki dečak voli da se igra.\<close>
text \<open>P2': Svaka devojčica voli da se igra.\<close> 
text \<open>P3': Dete je dečak ili je devojčica.\<close>

text \<open>(c) Na jeziku logike prvog reda zapisati sledeće rečenice i dokazati da su skupa nezadovoljive.\<close>

text \<open>- Svaka dva brata imaju zajedničkog roditelja.\<close>
text \<open>- Roditelj je stariji od deteta.\<close>
text \<open>- Postoje braća.\<close>
text \<open>- Nijedna osoba nije starija od druge.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Silogizmi]\<close>

text \<open>Barbara (AAA-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— All Greeks are mortal. (SaP)\<close>

lemma Barbara: (*<*) "undefined"
  oops (*>*)

text \<open>Celarent (EAE-1)\<close>
text \<open>Similar: Cesare (EAE-2)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— No snakes have fur. (SeP)\<close>

lemma Celarent: (*<*) "undefined" 
  oops (*>*)

text \<open>Ferioque (EIO-1)\<close>
text \<open>No homework is fun. (MeP)\<close>
text \<open>Some reading is homework. (SiM)\<close>
text \<open>— Some reading is not fun. (SoP)\<close>

lemma Ferioque: (*<*)"undefined"
  oops (*>*)


text \<open>Bocardo (OAO-3)\<close>
text \<open>Some cats are not pets. (MoP)\<close>
text \<open>All cats are mammals. (MaS)\<close>
text \<open>— Some mammals are not pets. (SoP)\<close>

lemma Bocardo:(*<*) "undefined"
  oops (*>*)

text \<open>Barbari (AAI-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— Some Greeks are mortal. (SiP)\<close>

lemma Barbari: (*<*)"undefined"
  oops (*>*)

text \<open>Celaront (EAO-1)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— Some snakes have no fur. (SoP)\<close>

lemma Celaront:(*<*) "undefined"
  oops (*>*)

text \<open>Camestros (AEO-2)\<close>
text \<open>All horses have hooves. (PaM)\<close>
text \<open>No humans have hooves. (SeM)\<close>
text \<open>— Some humans are not horses. (SoP)\<close>

lemma Camestros:(*<*) "undefined"
  oops (*>*)

text \<open>Felapton (EAO-3)\<close>
text \<open>No flowers are animals. (MeP)\<close>
text \<open>All flowers are plants. (MaS)\<close>
text \<open>— Some plants are not animals. (SoP)\<close>

lemma Felapton: (*<*) "undefined"
  oops (*>*)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Raymond M. Smullyan: Logical Labyrinths]\<close>

text \<open>Edgar Aberkrombi je bio antropolog koji se interesovao za logiku i socijologiju
      laganja i govorenja istine. Jednog dana je odlučio da poseti ostrvo vitezova i podanika.
      Stanovnike ovog ostrva delimo na one koji uvek govore istinu @{text "vitezove"} i
      one koji uvek govore laži @{text "podanike"}. Dodatno, na ostrvu žive samo vitezovi i 
      podanici. Aberkrombi susreće stanovnike i želi da prepozna ko je od njih vitez, 
      a ko je podatnik.\<close>

text \<open>1. Svaka osoba će odgovoriti potvrdno na pitanje: Da li si ti vitez?\<close>

lemma no_one_admit_knaves: (*<*) "undefined"
  oops  (*>*)

text \<open>1.1 Aberkombi je razgovarao sa tri stanovnika ostrva, označimo ih sa A, B i C. 
          Pitao je stanovnika A: ”Da li si ti vitez ili podanik?” 
          A je odgovorio ali nerazgovetno 
          pa je Aberkombi pitao stanovnika B: ”Šta je A rekao?” 
          B je odgovorio: ”Rekao je da je on podanik.” 
          Tada se uključila i osoba C i rekla: ”Ne veruj mu, on laže!” 
          Da li je osoba C vitez ili podanik?\<close>

lemma Smullyan_1_1:(*<*) "undefined"
  oops  (*>*)
 

text \<open>1.2 Aberkombi je pitao 
          stanovnika A koliko među njima trojicom ima podanika. 
          A je opet odgovorio nerazgovetno,
          tako da je Aberkombi pitao stanovnika B šta je A rekao. 
          B je rekao da je A rekao da su tačno dvojica podanici. 
          Ponovo je stanovnik C tvrdio da B laže. 
          Da li je u ovoj situaciji moguće odrediti da li je C vitez ili podanik?\<close>

lemma Smullyan_1_2:(*<*) "undefined"
  oops (*>*)

text \<open>1.3 Da li se zaključak prethodnog tvrđenja menja ako B promeni svoj odgovor 
          i kaže da je A rekao da su tačno dva od njih vitezovi?\<close>

lemma Smullyan_1_3:(*<*) "undefined"
  oops  (*>*)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
