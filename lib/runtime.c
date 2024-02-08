#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdlib.h>

void printInt(int n)
{
    printf("%d\n", n);
}

void printString(char *str)
{
    if (str != NULL)
        printf("%s\n", str);
}

void error()
{
    fprintf(stderr, "runtime error\n");
    exit(1);
}

int readInt() 
{
    int n;
    if (scanf("%d\n", &n) < 0)
        error();
    
    return n;
}

char* readString() 
{
    char *str = NULL;
    size_t ss;
    size_t s = getline(&str, &ss, stdin);

    if (s == -1) 
        error();

    str[s - 1] = '\0';
    return str;
}

char* __addStrings(char *str1, char *str2)
{
    if (str1 == NULL)
        return str2;
    else if (str2 == NULL)
        return str1;

    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);

    size_t s = len1 + len2 + 1;

    char* res = malloc(sizeof(char) * s);
    memcpy(res, str1, len1);
    memcpy(res + len1, str2, len2);
    res[s - 1] = 0;

    return res;
}

int __eqStrings(char *str1, char *str2)
{
    return strcmp(str1, str2) == 0;
}

char* __calloc(int size) 
{
    return (char*) calloc(1, size);
}
