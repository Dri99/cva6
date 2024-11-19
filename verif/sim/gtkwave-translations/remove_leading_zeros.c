#include <stdio.h>
int main(int argc, char **argv)
{
    while(!feof(stdin))
    {
        char buf[1025];
        buf[0] = 0;
        fscanf(stdin, "%s", buf);
        if(buf[0])
        {
            int i=0;
            while(buf[i]=='0')
                i++;
            int j=0;
            do{
                buf[j]=buf[i];
                i++;
                j++;
            }while(buf[j]!='\0');
            printf("%s\n", buf);
            fflush(stdout);
        }
    }
    return(0);
}