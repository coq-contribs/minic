#define LOW( a )	(*( (char *)(&a) ))
#define HIGH( a )	(*( (char *)(&(a))+1 ))

#include <stdio.h>

typedef void* gpointer;

#define g_malloc(size)	     (gpointer) malloc(size)
#define g_new(type, count)	  \
    ((type *) g_malloc ((unsigned) sizeof (type) * (count)))
#define g_free(mem)	     free(mem)

typedef struct {
 float real1,real2; 
 int   intg;}
 mystruct;

mystruct s1,s2;
int   intg;
float r;


int b1,b2;

/* Pueden haber labels repetidos, como intg en mystruct y en mystruct2 */
typedef struct {
mystruct fandi;
 int   intg;}
 mystruct2;

mystruct2 s;
mystruct *ps;

int fi (int i,int x){
printf("I'm f%d\n",i);
return (x);}

void g (int x){
return; 
}
/* No se puede asociar una expresion como valor inicial de una variable
   global.
int tt = fi(2,1);
int tt = s1.intg;
*/

main (){
int *p = NULL;
int x  = 5;
int i;
/* valido :
int i  = fi(2,x);
*/
char *q1;
char *q2;
int  ar [32];
int  arr[32][32];

/* Vision de direcciones como arboles es correcta:
s1.real1= 1.0;
s1.real2=2.0;
s1.intg = 3;
if (&(s1.real2) == (&(s1.real1)+1)) {printf("true");} else {printf("false");}
*/

/* El indice de un array en una asignacion puede ser cualquier expresion.
   Se evalua primero la expresion a la IZQUIERDA de la asignacion.

ar[fi(1,1)] = fi(2,2);
*/

/* Los indices de un array son evaluados de izq a der.
arr[32][32] = 5;
i = arr[fi(1,32)][fi(2,32)];
*/

/* The initial value in a for loop is calculated only once.
for (i=fi(1,0);i<fi(2,3);fi(3,1)){printf("body\n");};
*/

/* A for loop may not stop.
for (1;1;1){printf("body\n");};
*/

/* Plus est evalu de gauche  droite 
i = f1(1) + f2(2);
*/

/* And est evalue de gauche  droite 
i = f1(1) & f2(2);
*/

/* Appel de fonction est de gauche  droite 
i = fbin(f1(1), f2(2));
*/

/* On peut caster des expressions complexes.
r = (int)(1.0 + 0.1);
printf("%d\n",r);
*/

ps = &(s.fandi);
ps -> real1 = 3.0;
ps -> real2 = 6.0;
ps -> intg  = 4;

q2 = g_new(char,32);
q1 = q2;
for (i=0;i <32;i++){*q2='a';q2++;};
/*
s2.real = 1.0;
s2.intg = f(70);
s1 = s2;
p  = &x;
 *(f(3)) = 4; */
57;
/* valid : *p = 3; */
HIGH(x)=3;
printf("%s",x);


/*b1 = fi(130,1) && fi(131,1);*/

}
