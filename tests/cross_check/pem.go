// Reads one request per line and prints what Go's encoding/pem makes of
// it. Used by tests/cross_check.py.
//
//   enc LABEL;DATA   the label's character codes and the bytes, as
//                    comma-separated decimal numbers; prints "ok:" and the
//                    character codes of pem.EncodeToMemory, or "none" on
//                    an error
//   dec TEXT         the text's character codes; prints "ok:", the type's
//                    character codes, ";", the bytes, ";", and the number
//                    of bytes pem.Decode left over; or "none" when it finds
//                    no block
package main

import (
	"bufio"
	"encoding/pem"
	"fmt"
	"os"
	"strconv"
	"strings"
)

func numbers(s string) []int {
	out := []int{}
	if s == "" {
		return out
	}
	for _, f := range strings.Split(s, ",") {
		n, _ := strconv.Atoi(f)
		out = append(out, n)
	}
	return out
}

func text(ns []int) string {
	var b strings.Builder
	for _, n := range ns {
		b.WriteRune(rune(n))
	}
	return b.String()
}

func codes(s string) string {
	parts := []string{}
	for _, r := range s {
		parts = append(parts, strconv.Itoa(int(r)))
	}
	return strings.Join(parts, ",")
}

func bytesOut(b []byte) string {
	parts := make([]string, len(b))
	for i, x := range b {
		parts[i] = strconv.Itoa(int(x))
	}
	return strings.Join(parts, ",")
}

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<26)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		op, arg, _ := strings.Cut(in.Text(), " ")
		switch op {
		case "enc":
			l, d, _ := strings.Cut(arg, ";")
			data := []byte{}
			for _, n := range numbers(d) {
				data = append(data, byte(n))
			}
			enc := pem.EncodeToMemory(&pem.Block{Type: text(numbers(l)), Bytes: data})
			if enc == nil {
				fmt.Fprintln(out, "none")
			} else {
				fmt.Fprintln(out, "ok:"+codes(string(enc)))
			}
		case "dec":
			block, rest := pem.Decode([]byte(text(numbers(arg))))
			if block == nil {
				fmt.Fprintln(out, "none")
			} else {
				fmt.Fprintf(out, "ok:%s;%s;%d\n", codes(block.Type), bytesOut(block.Bytes), len(rest))
			}
		}
	}
	if err := in.Err(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
