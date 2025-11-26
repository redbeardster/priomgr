#!/bin/bash

# Скрипт для запуска всех видов верификации Priority Manager

set -e

echo "🔬 === ПОЛНАЯ ВЕРИФИКАЦИЯ PRIORITY MANAGER ==="
echo

# Цвета для вывода
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Функция для вывода статуса
print_status() {
    if [ $1 -eq 0 ]; then
        echo -e "${GREEN}✅ $2 PASSED${NC}"
    else
        echo -e "${RED}❌ $2 FAILED${NC}"
    fi
}

# Счётчики
TOTAL=0
PASSED=0

# 1. Rust Type Checking
echo -e "${BLUE}[1/5] Rust Type Checking...${NC}"
TOTAL=$((TOTAL + 1))
if cargo check 2>&1 | grep -q "Finished"; then
    print_status 0 "Rust Type Checking"
    PASSED=$((PASSED + 1))
else
    print_status 1 "Rust Type Checking"
fi
echo

# 2. Rust Tests
echo -e "${BLUE}[2/5] Rust Unit Tests...${NC}"
TOTAL=$((TOTAL + 1))
if cargo test --lib 2>&1 | grep -q "test result: ok"; then
    print_status 0 "Rust Unit Tests"
    PASSED=$((PASSED + 1))
else
    print_status 1 "Rust Unit Tests"
fi
echo

# 3. TLA+ Model Checking
echo -e "${BLUE}[3/5] TLA+ Model Checking...${NC}"
TOTAL=$((TOTAL + 1))
if command -v java &> /dev/null; then
    TLA_TOOLS="$HOME/.vscode/extensions/tlaplus.vscode-ide-2025.11.241836/tools/tla2tools.jar"
    if [ -f "$TLA_TOOLS" ]; then
        if java -cp "$TLA_TOOLS" tlc2.TLC PriorityManagerSimple.tla -config PriorityManagerSimple.cfg 2>&1 | grep -q "No error has been found"; then
            print_status 0 "TLA+ Model Checking"
            PASSED=$((PASSED + 1))
        else
            print_status 1 "TLA+ Model Checking"
        fi
    else
        echo -e "${YELLOW}⚠️  TLA+ tools not found, skipping${NC}"
    fi
else
    echo -e "${YELLOW}⚠️  Java not found, skipping TLA+${NC}"
fi
echo

# 4. Kani Verification
echo -e "${BLUE}[4/5] Kani Bounded Model Checking...${NC}"
TOTAL=$((TOTAL + 1))
if command -v cargo-kani &> /dev/null; then
    if cargo kani 2>&1 | grep -q "VERIFICATION:- SUCCESSFUL"; then
        print_status 0 "Kani Verification"
        PASSED=$((PASSED + 1))
    else
        print_status 1 "Kani Verification"
    fi
else
    echo -e "${YELLOW}⚠️  Kani not installed, skipping${NC}"
    echo "   Install: cargo install --locked kani-verifier && cargo kani setup"
fi
echo

# 5. Prusti Verification
echo -e "${BLUE}[5/5] Prusti Deductive Verification...${NC}"
TOTAL=$((TOTAL + 1))
if command -v cargo-prusti &> /dev/null; then
    if cargo prusti 2>&1 | grep -q "Verification successful"; then
        print_status 0 "Prusti Verification"
        PASSED=$((PASSED + 1))
    else
        print_status 1 "Prusti Verification"
    fi
else
    echo -e "${YELLOW}⚠️  Prusti not installed, skipping${NC}"
    echo "   Install: cargo install prusti-cli"
fi
echo

# Итоговая статистика
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo -e "${BLUE}📊 ИТОГОВАЯ СТАТИСТИКА${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Проверок выполнено: $PASSED / $TOTAL"

if [ $PASSED -eq $TOTAL ]; then
    echo -e "${GREEN}🎉 ВСЕ ПРОВЕРКИ ПРОЙДЕНЫ!${NC}"
    exit 0
elif [ $PASSED -gt 0 ]; then
    echo -e "${YELLOW}⚠️  ЧАСТИЧНЫЙ УСПЕХ${NC}"
    exit 1
else
    echo -e "${RED}❌ ВСЕ ПРОВЕРКИ ПРОВАЛЕНЫ${NC}"
    exit 1
fi
