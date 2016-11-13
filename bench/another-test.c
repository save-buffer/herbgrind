#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include "herbgrind.h"

double foo(double x){
  double f = 1e16 + x;
  return f - 1e16;
}

int main(int argc, char** argv){
  double result = 0;
  HERBGRIND_BEGIN();
  result = foo(1);
  HERBGRIND_MARK_IMPORTANT(result);
  HERBGRIND_END();
  printf("result is %e\n", result);
}
