/* Test 1:
int i,y = 1;
int x = 2;
main(){
for(i=3;i>0;i--){y = (y*y);};
printf("%d\n",y);
}
*/

int x   = 2;
int pot3 (){
 int i,y = 1;
 for(i=3;i>0;i--){y = (y+y);};
 return y;
}
main (){
 x = pot3();
 printf("%d\n",x);
}
