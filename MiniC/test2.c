typedef struct {
 float toto;
} sub;

typedef struct {
 float real1,toto; 
 sub * substruct;
 float * tata;
 float dodo[25];
}
 mystruct;

typedef struct {
 float real1; 
 sub   substruct;
}
 mystruct1;

typedef struct {
 sub   substruct;
 float real1; 
}
 mystruct2;

mystruct1 xx;
mystruct2 yy;


mystruct y;
mystruct y2;
float    f;
sub x;

mystruct ff(mystruct z){
return z;
  };

main (){
y.real1 = 2.0;
y.toto  = 3.0;
y.substruct = 0;
y2=y;
printf("%f\n",y2.toto);

}
