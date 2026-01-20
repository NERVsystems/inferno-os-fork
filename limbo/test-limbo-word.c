#include "lib9.h"
#include "isa.h"
#include <stdio.h>

int main() {
    printf("NREG=%d\n", NREG);
    printf("IBY2WD=%d\n", IBY2WD);
    printf("sizeof(void*)=%zu\n", sizeof(void*));
    printf("STemp=%d\n", NREG * IBY2WD);
    printf("MaxTemp=%d\n", NREG * IBY2WD + 3 * IBY2WD);
    return 0;
}
