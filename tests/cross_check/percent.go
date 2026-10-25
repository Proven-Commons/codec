// Reads one text per line, as comma-separated decimal character codes,
// and prints what Go's net/url.PathUnescape makes of it: "ok:" and the
// bytes as comma-separated decimal numbers, or "none" when it returns an
// error. Used by tests/cross_check.py.
package main

import (
	"bufio"
	"fmt"
	"net/url"
	"os"
	"strconv"
	"strings"
)

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<24)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		var text strings.Builder
		if line := in.Text(); line != "" {
			for _, field := range strings.Split(line, ",") {
				n, _ := strconv.Atoi(field)
				text.WriteRune(rune(n))
			}
		}
		b, err := url.PathUnescape(text.String())
		if err != nil {
			fmt.Fprintln(out, "none")
			continue
		}
		parts := make([]string, len(b))
		for i := 0; i < len(b); i++ {
			parts[i] = strconv.Itoa(int(b[i]))
		}
		fmt.Fprintln(out, "ok:"+strings.Join(parts, ","))
	}
}
