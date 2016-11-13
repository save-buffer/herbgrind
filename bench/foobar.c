#include <stdio.h>
#include "herbgrind.h"

double foo(double* xs, double* ys){
  return ((xs[0] + xs[1]) - (ys[0] + ys[1])) * xs[0];
}

double bar(double x, double y, double z){
  double xy[2] = {x, y};
  double xz[2] = {x, z};
  return foo(xy, xz);
}

int main(int argc, char** argv){
  HERBGRIND_BEGIN();
  double a = bar(10, 7, 8);
  double b = bar(10e15, 1, 0);
  double c = bar(1, 0, 3);

  double d = (b / a) * c;
  HERBGRIND_MARK_IMPORTANT(d);

  printf("%e\n", d);
  HERBGRIND_END();
}
