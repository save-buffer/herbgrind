#include <stdio.h>
#include <math.h>

int main(int argc, char** argv){
  double x, y;
  x = atan(1.0) * (40002);
  y = tan(x) - (sin(x)/cos(x));
  printf("%e\n", y);
  return 0;
}
