#include <stdio.h>
#include "herbgrind.h"

double foobar(double x, double y, double z){
  return (y - z) * x;
}

int main(int argc, char** argv){
  HERBGRIND_BEGIN();
  double a = foobar(10, 7, 8);
  double b = foobar(1e16, 1, 0);
  double c = foobar(1, 0, 3);

  printf("%e\n", (b / a) * c);
  HERBGRIND_END();
}
