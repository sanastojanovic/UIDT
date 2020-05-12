theory mr17283_Strahinja_Trninic
  imports Main
begin

text \<open>
                      Isabelle projekat

Predmet: Uvod u interaktivno dokazivanje teorema
Profesor: prof. dr. Filip Maric
Asistent: prof. dr. Sana Stojanovic Djurdjevic

Student: Strahinja Trninic
Indeks: mr17283
Grupa: 4R

Zadatak: 
        51. Internacionalna Matematicka Olimpijada
                    Astana, Kazahstan, 2010.

            Lista problema sa resenjima
            -Kombinatorni zadatak: C3-

(https://www.imo-official.org/problems/IMO2010SL.pdf)
\<close>


text \<open>
Kratak opisa zadatka:

Data je sahovska tabla dimenzije 100\<times>100. Potrebno je pronaci broj razlicitih nacina
na koje mogu da se poredjaju 2500 kraljeva, pazeci na uslove:
pazeci na sledece uslove:
- Kraljevi ne semju da napadaju jedni druge
- Svaki red i svaka kolona moraju da sadrze tacno 25 kraljeva
- Cak iako se jedna konfiguracija moze dobiti od druge rotacijama ili simetrijama,
  one se idalje tretiraju kao dve razlicite konfiguracije.
\<close>


section \<open>Tabla\<close>

text \<open>Definisemo tablu za igranje\<close>


text \<open>Prvo polje je dole-levo i ima koordinate (0, 0) a poslednje je gore-desno i ima koordinate (9, 9)\<close>

datatype broj = nula ("\<zero>") | jedan ("\<one>") | dva ("\<two>") | tri ("\<three>") | cetiri ("\<four>") | pet ("\<five>") | sest ("\<six>") | sedam ("\<seven>") | osam ("\<eight>") | devet ("\<nine>") (*| 
                deset ("\<one>\<zero>") | jedanaest ("\<one>\<one>") | dvanaest ("\<one>\<two>") | trinaest ("\<one>\<three>") | cetrnaest ("\<one>\<four>") | petnaest ("\<one>\<five>") | sesnaest ("\<one>\<six>") | sedamnaest ("\<one>\<seven>") | osamnaest ("\<one>\<eight>") | deventaest ("\<one>\<nine>") |
                ddeset ("\<two>\<zero>") | djedan ("\<two>\<one>") | ddva ("\<two>\<two>") | dtri ("\<two>\<three>") | dcetiri ("\<two>\<four>") | dpet ("\<two>\<five>") | dsest ("\<two>\<six>") | dsedam ("\<two>\<seven>") | dosam ("\<two>\<eight>") | ddevet ("\<two>\<nine>") |
                tdeset ("\<three>\<zero>") | tjedan ("\<three>\<one>") | tdva ("\<three>\<two>") | ttri ("\<three>\<three>") | tcetiri ("\<three>\<four>") | tpet ("\<three>\<five>") | tsest ("\<three>\<six>") | tsedam ("\<three>\<seven>") | tosam ("\<three>\<eight>") | tdevet ("\<three>\<nine>") |
                cdeset ("\<four>\<zero>") | cjedan ("\<four>\<one>") | cdva ("\<four>\<two>") | ctri ("\<four>\<three>") | ccetiri ("\<four>\<four>") | cpet ("\<four>\<five>") | csest ("\<four>\<six>") | csedam ("\<four>\<seven>") | cosam ("\<four>\<eight>") | cdevet ("\<four>\<nine>") |
                pdeset ("\<five>\<zero>") | pjedan ("\<five>\<one>") | pdva ("\<five>\<two>") | ptri ("\<five>\<three>") | pcetiri ("\<five>\<four>") | ppet ("\<five>\<five>") | psest ("\<five>\<six>") | psedam ("\<five>\<seven>") | posam ("\<five>\<eight>") | pdevet ("\<five>\<nine>") |
                sdeset ("\<six>\<zero>") | sjedan ("\<six>\<one>") | sdva ("\<six>\<two>") | stri ("\<six>\<three>") | scetiri ("\<six>\<four>") | spet ("\<six>\<five>") | ssest ("\<six>\<six>") | ssedam ("\<six>\<seven>") | sosam ("\<six>\<eight>") | sdevet ("\<six>\<nine>") |
                sedeset ("\<seven>\<zero>") | sejedan ("\<seven>\<one>") | sedva ("\<seven>\<two>") | setri ("\<seven>\<three>") | secetiri ("\<seven>\<four>") | sepet ("\<seven>\<five>") | sesest ("7\<six>") | sesedam ("\<seven>\<seven>") | seosam ("\<seven>\<eight>") | sedevet ("\<seven>\<nine>") |
                odeset ("\<eight>\<zero>") | ojedan ("\<eight>\<one>") | odva ("\<eight>\<two>") | otri ("\<eight>\<three>") | ocetiri ("\<eight>\<four>") | opet ("\<eight>\<five>") | osest ("\<eight>\<six>") | osedam ("\<eight>\<seven>") | oosam ("\<eight>\<eight>") | odevet ("\<eight>\<nine>") |
                dedeset ("\<nine>\<zero>") | dejedan ("\<nine>\<one>") | dedva ("\<nine>\<two>") | detri ("\<nine>\<three>") | decetiri ("\<nine>\<four>") | depet ("\<nine>\<five>") | desest ("\<nine>\<six>") | desedam ("\<nine>\<seven>") | deosam ("\<nine>\<eight>") | dedevet ("\<nine>\<nine>")*)

type_synonym polje = "broj \<times> broj"

locale Igra = 

  fixes sledbenik :: "broj \<Rightarrow> broj"
  assumes sledbenik_Eksplicitno: "sledbenik x = (if x = \<zero> then \<one> else if x = \<one> then \<two> else if x = \<two> then \<three> else if x = \<three> then \<four> else if x = \<four> then \<five> else if x = \<five> then \<six> else if x = \<six> then \<seven> else if x = \<seven> then \<eight> else \<nine>)"
  (*
  else if x = \<one>\<zero> then \<one>\<one> else if x = \<one>\<two> then ...
  *)
  fixes m0nus1 :: "broj \<Rightarrow> broj"
  assumes m0nus1_Eksplicitno: "m0nus1 x = (if x = \<nine> then \<eight> else if x = \<eight> then \<seven> else if x = \<seven> then \<six> else if x = \<six> then \<five> else if x = \<five> then \<four> else if x = \<four> then \<three> else if x = \<three> then \<two> else if x = \<two> then \<one> else \<zero>)"

  fixes vece :: "broj \<Rightarrow> broj \<Rightarrow> bool" (infixl "\<prec>" 100)
  assumes vece_IRefl: "\<forall>x.(\<not>(x \<prec> x))"
  assumes vece_Trans: "\<forall>x y z.(x \<prec> y \<and> y \<prec> z \<longrightarrow> x \<prec> z)"
  assumes vece_Sledbenik: "\<forall>x.(x \<prec> (sledbenik x))"

  fixes ima_kralj :: "broj \<Rightarrow> broj \<Rightarrow> bool"

  assumes vrsta_Tacno25: "\<forall>x y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25.
                  (ima_kralj x y1 \<and> ima_kralj x y2 \<and> ima_kralj x y3 \<and> ima_kralj x y4 \<and> ima_kralj x y5 \<and> ima_kralj x y6 \<and> ima_kralj x y7 \<and> ima_kralj x y8 \<and> ima_kralj x y8 \<and> ima_kralj x y9 \<and> ima_kralj x y10 \<and> ima_kralj x y11 \<and> ima_kralj x y12 \<and> ima_kralj x y13 \<and> ima_kralj x y14 \<and> ima_kralj x y15 \<and> ima_kralj x y16 \<and> ima_kralj x y17 \<and> ima_kralj x y18 \<and> ima_kralj x y19 \<and> ima_kralj x y20 \<and> ima_kralj x y21 \<and> ima_kralj x y22 \<and> ima_kralj x y23 \<and> ima_kralj x y24 \<and> ima_kralj x y25
                   \<and> (\<forall>t.(t \<notin> {y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25} \<longrightarrow> \<not>ima_kralj x t)))"

  assumes kolona_Tacno25: "\<forall>y x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25.
                  (ima_kralj y x1 \<and> ima_kralj y x2 \<and> ima_kralj y x3 \<and> ima_kralj y x4 \<and> ima_kralj y x5 \<and> ima_kralj y x6 \<and> ima_kralj y x7 \<and> ima_kralj y x8 \<and> ima_kralj y x8 \<and> ima_kralj y x9 \<and> ima_kralj y x10 \<and> ima_kralj y x11 \<and> ima_kralj y x12 \<and> ima_kralj y x13 \<and> ima_kralj y x14 \<and> ima_kralj y x15 \<and> ima_kralj y x16 \<and> ima_kralj y x17 \<and> ima_kralj y x18 \<and> ima_kralj y x19 \<and> ima_kralj y x20 \<and> ima_kralj y x21 \<and> ima_kralj y x22 \<and> ima_kralj y x23 \<and> ima_kralj y x24 \<and> ima_kralj y x25
                   \<and> (\<forall>t.(t \<notin> {x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25} \<longrightarrow> \<not>ima_kralj t y)))"



begin
text \<open>Neke provere\<close>

lemma "\<two> \<prec> \<eight>"
  by (metis broj.distinct(11) broj.distinct(13) broj.distinct(19) broj.distinct(21) broj.distinct(23) broj.distinct(25) broj.distinct(27) broj.distinct(29) broj.distinct(3) broj.distinct(35) broj.distinct(37) broj.distinct(39) broj.distinct(41) broj.distinct(43) broj.distinct(49) broj.distinct(5) broj.distinct(51) broj.distinct(53) broj.distinct(55) broj.distinct(61) broj.distinct(63) broj.distinct(65) broj.distinct(7) broj.distinct(71) broj.distinct(73) broj.distinct(79) broj.distinct(9) sledbenik_Eksplicitno vece_Sledbenik vece_Trans)

lemma vece_Najmanje: "\<forall>x.(\<zero> \<prec> x)"
  by (metis broj.distinct(17) broj.distinct(33) broj.distinct(47) broj.distinct(59) broj.distinct(69) broj.distinct(77) broj.distinct(83) broj.distinct(87) sledbenik_Eksplicitno vece_IRefl vece_Sledbenik)

lemma vece_Najvece: "\<forall>x.(\<not>(\<nine> \<prec> x))"
  by (metis broj.distinct(17) broj.distinct(33) broj.distinct(47) broj.distinct(59) broj.distinct(69) broj.distinct(77) broj.distinct(83) broj.distinct(87) sledbenik_Eksplicitno vece_IRefl vece_Sledbenik)



end


end