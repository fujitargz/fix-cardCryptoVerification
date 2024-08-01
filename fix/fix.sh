echo -e "========================\nsecurity\n========================\n"

gcc -o security -D WEAK_SECURITY=0 security.c && ./security
rm security

echo -e "\n========================\ncorrectness\n========================\n"

gcc -o correctness -D WEAK_SECURITY=0 correctness.c && ./correctness
rm correctness

echo -e "\n========================\nprobability calculation\n========================\n"

gcc -o probCalc -D WEAK_SECURITY=0 probCalc.c && ./probCalc
rm probCalc