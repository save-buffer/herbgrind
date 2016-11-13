#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include "herbgrind.h"

#define COUNT 1000

double range_rand(double min, double max){
  volatile double k = rand();
  double f = (double)k / RAND_MAX;
  double maxMINUSmin = max - min;
  return min + f * maxMINUSmin;
}

int main(int argc, char** argv){
  double values[COUNT];
  HERBGRIND_BEGIN();
  for (int i = 0; i < COUNT; ++i){
    values[i] = range_rand(0, FLT_MAX / COUNT);
  }
  volatile double acc = 0;
  for (int i = 0; i < COUNT; ++i){
    acc = acc + values[i];
  }
  HERBGRIND_MARK_IMPORTANT(acc);
  HERBGRIND_END();
  printf("sum is: %e\n", acc);
}
