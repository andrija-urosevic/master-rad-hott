Ovaj paket sadrži stil teza Matematičkog fakulteta, Univerziteta u
Beogradu. Stil je kreiran na osnovu uputstva Univerziteta u Beogradu.

**Autor**: Filip Marić
**Verzija**: 1.0
**Datum**: Oktobar 2015.

Ovaj dokument sadrži uputstvo za instalaciju i podešavanje odgovarajućih TeX
sistema, fontova, integrisanih okruženja i slično. Postupak instalacije šablona
teza i pratećih datoteka je trivijalan i podrazumeva samo raspakivanje zip
datoteke matfteze.zip. Ipak, da bi se stil mogao koristiti potrebno je da je
na računaru instaliran i ispravno podešen neki LaTeX sistem novijeg datuma.

# Ubuntu Linux

Ako se koristi operativni sistem Ubuntu Linux, preporučuje se instalacija
sledećih Ubuntu paketa:

  - `texlive-full` - TeXLive system (full installation, potrebna
                       verzija bar 2014)
  - `cm-super` - TeX font package (full version) with CM (EC) in Type1
                   in T1, T2*, TS1, X2 encoding

Prvi paket (`texlive-full`) predstavlja punu instalaciju TeXLive
sistema (instalacija može da traje neko vreme i da zauzme malo veći
prostor na disku, ali kasnije nije potrebno posebno instalirati
pojedinačne pakete), dok drugi paket (`cm-super`) sadrži vektorske
(Adobe Type1) verzije Computer Modern fontova u kodiranjima T1 i T2A
koji se koriste u tezama ako se koristi pdflatex (osnovni TeXLive
sistem sadrži samo rasterske fontove u ovim kodiranjima i generisani
pdf će biti ružan). Naravno, umesto pune instalacije TeXLive sistema,
moguće je instalirati samo osnovnu verziju (ubuntu paket texlive), a
kasnije ručno dodavati pojedinačne potrebne pakete.

Instalacija Ubuntu paketa se najlakše vrši iz komandne linje komandom:

~~~
   sudo apt-get install <paket>
~~~

Na primer:

~~~
   sudo apt-get install texlive-full
~~~

Tokom instalacije je potrebno imati vezu sa internetom (ako se
instalacija vrši na fakultetu, potrebno je podesiti i proxy server).

## Instalacija fontova za XeLaTeX

Ako se koristi xelatex umesto pdflatex-a (a to preporučujem) potrebno
je dodatno instalirati sistemske fontove (xelatex omogućava da LaTeX
koristi sistemske TrueType i OpenType fontove u Unicode kodiranju). U
tezi se koristi font Computer Modern Unicode koji se može instalirati
instalacijom Ubuntu paketa:

  - `fonts-cmu` - Computer Modern Unicode fonts

Takođe, koristi se i font OpenSans koji Vam isporučujemo u
direktorijumu:

  - `fonts/OpenSans/*`

Instalacija se vrši na uobičajen način (na primer, klikom na ttf
datoteku otvara se FontViewer i font se instalira komandom install).

## Instalacija programa Biber

Sistem BibLaTeX i program Biber zamenjuju pomalo zastareli program
BibTeX i omogućavaju korišćenje višejezičke bibliografije i punu
podršku za Unicode u bibliografskim referencama. Biber se instalira
pomoću Ubuntu paketa:

  - `biber` - BibLaTeX backend 


# Microsoft Windows

Ako se koristi operativni sistem Microsoft Windows, obično se za TeX
koristi instalacija sistema MiKTeX. Iako je disertacije koje prate ove
šablone moguće prevoditi i sa osnovnom, nepodešenom verzijom sistema
MiKTeX, da bi se postigao zadovoljavajući kvalitet proizvednih PDF
dokumenata potrebno je izvršiti određena podešavanja sistema
(instaliranje dodatnih paketa, fontova i slično).

Minimalna instalacija MiKTeX sistema ne sadrži sve potrebne LaTeX
pakete, ali se oni automatski preuzimaju sa interneta i instaliraju
kada zatrebaju prilikom prevođenja dokumenta. Potrebno je samo nakon
svakog pitanja sistema potvrditi da ste saglasni da se odgovarajući
paket preuzme iz repozitorijuma sa interneta i instalira. Na žalost,
neka integrisana okruženja (npr. WinEdt) nekada ne mogu da pokrenu
instalaciju nedostajućih paketa i tada je poželjno prevođenje
pokrenuti iz komandne linije (Win+R cmd i onda "pdflatex
matfdoktorat-primer" u odgovarajućem direktorijumu). Moguće varijante
su i da se instalira pun sistem MiKTeX ili da se ručno instaliraju svi
paketi koji se koriste u tezama (paketi se instaliraju iz programa
MiKTeX Package Manager koji je instaliran prilikom instalacije MiKTeX
sistema). U stilu teza se direktno koriste paketi: `babel-english`,
`babel-serbian`, `cyrillic`, `pdfpages`, `csquotes`, `biblatex`,
`opensans`, `polyglossia` i posredno paketi: `lh`, `etoolbox`,
`eso-pic`, `xcolor`, `logreq`, `mtopdf`, `makecmds`, `l3kernel`,
`l3packages`, `tipa`, `xetex-def`.

## Instalacija fontova

Ako se koristi pdflatex, obavezno se preporučuje instalacija MiKTeX
paketa `cm-super` jer on sadrži vektorske verzije (Adobe Type 1)
Computer Modern fontova. Instalacija se može izvršiti korišćenjem
programa *MiKTeX Console* koji je instaliran prilikom instalacije
MiKTeX sistema. Ako je sistem noviji onda poželjno instalirati i paket
`cmsrb` koji razrešava problem pogrešnih ćiriličkih italic fontova
(ako je taj paket uspešno instaliran, potrebno ga je ručno uključiti u
`tex` preambuli).

Da bi se mogao koristiti XeLaTeX (što toplo preporučujem) potrebno je
dodatno instalirati sistemske fontove (xelatex omogućava da LaTeX
koristi sistemske TrueType i OpenType fontove u Unicode kodiranju). U
tezi se koristi fontovi *Computer Modern Unicode* i *Open Sans* i oba
fonta vam isporučujemo u direktorijumima

  - `fonts/CMU/*`
  - `fonts/OpenSans/*`

Postupak instalacije je uobičajen (selektuju se sve .ttf tj. .otf
datoteke i iz kontekstnog menija koji se pokreće desnim klikom miša se
odabere Install). Napomena: prvo prevođenje xelatex-om nakon
instalacije fontova može trajati duže, dok se ne izgradi takozvani
font cache.

# Neki problemi

## Automatski prelom reči

U starijim verzijama MikTeX-a se može desiti da obrasci hifenacije
(preloma reči na kraju reči) za srpski jezik ćiriličkim pismom nisu
instalirani kako treba, potrebno je nakon instalacije izvršiti
određena podešavanja. To se može prepoznati tako što se vidi
upozorenje

~~~
Package babel Warning: No hyphenation patterns were loaded for
(babel)                the language `serbianc'
(babel)                I will use the patterns loaded for english
                       language instead.
~~~

To se može popraviti tako što se pronađe datoteka language.dat (ona se često
nalazi u direktorijumu `C:\ProgramData\MiKTeX\2.9\tex\generic\config` ili
`C:\Users\<Name>\AppData\Roaming\MiKTeX\2.9\tex\generic\config`), u nju doda
linija:

~~~
serbianc loadhyph-sr-cyrl.tex
~~~

i na kraju iz komandne linije (Win+R, `cmd`) pokrene `initexmf
--dump`. Napomena: jezička podešavanja se obično vrše iz programa
MiKTeX Settings, na kartici language, međutim, u starijim verzijama je
ponuđen samo jezik `serbian` (latiničko pismo), a ne i `serbianc`
(ćiriličko pismo), tako da je dodavanje podrške za hifenaciju
ćiriličkih dokumenata neophodno ručno izvršiti (na opisani način).

## Vektorski fontovi

Ako se i nakon instalacije paketa `cm-super` i dalje prikazuju rasterski
fontovi, potrebno je ažurirati mape fontova tako što se iz komandne linije
(koja se pokreće tako što se pritisne `Win + R` i otkuca `cmd`) pokrene
komanda

~~~
updmap
~~~

Još jedna komanda koja može pomoći oko problema sa fontovima  je 

~~~
initexmf --mkmaps
~~~
