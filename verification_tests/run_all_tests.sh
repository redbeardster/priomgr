#!/bin/bash
# Скрипт для запуска всех тестов верификации

set -e

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║                                                           ║"
echo "║   ЗАПУСК ВСЕХ ТЕСТОВ ВЕРИФИКАЦИИ                          ║"
echo "║                                                           ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""

# Цвета для вывода
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Функция для запуска теста
run_test() {
    local name=$1
    local command=$2
    local dir=$3
    
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}▶ $name${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    if [ -n "$dir" ]; then
        cd "$dir"
    fi
    
    if eval "$command"; then
        echo ""
        echo -e "${GREEN}✓ $name: PASSED${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo ""
        echo -e "${RED}✗ $name: FAILED${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
    
    if [ -n "$dir" ]; then
        cd - > /dev/null
    fi
    
    echo ""
}

# 1. Property-based тесты
run_test "Property-Based Tests (PropTest)" \
    "cargo test --release" \
    "property_tests"

# 2. Prusti верификация
if command -v cargo-prusti &> /dev/null; then
    run_test "Prusti Deductive Verification" \
        "cargo prusti --features prusti" \
        "prusti"
else
    echo -e "${YELLOW}⚠ Prusti не установлен, запускаем обычные тесты${NC}"
    run_test "Prusti Unit Tests (без верификации)" \
        "cargo test" \
        "prusti"
    echo "  Для полной верификации установите: cargo install prusti-cli"
    echo ""
fi

# 3. Kani верификация
if command -v cargo-kani &> /dev/null; then
    run_test "Kani Bounded Model Checking" \
        "cargo kani" \
        "kani"
else
    echo -e "${YELLOW}⚠ Kani не установлен, пропускаем${NC}"
    echo "  Установка: cargo install --locked kani-verifier && cargo kani setup"
    echo ""
fi

# 4. Обычные unit тесты
run_test "Unit Tests (Prusti)" \
    "cargo test" \
    "prusti"

run_test "Unit Tests (Kani)" \
    "cargo test" \
    "kani"

# Итоговая статистика
echo ""
echo "╔═══════════════════════════════════════════════════════════╗"
echo "║                                                           ║"
echo "║   ИТОГОВАЯ СТАТИСТИКА                                     ║"
echo "║                                                           ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""
echo -e "Всего тестов:    ${BLUE}$TOTAL_TESTS${NC}"
echo -e "Пройдено:        ${GREEN}$PASSED_TESTS${NC}"
echo -e "Провалено:       ${RED}$FAILED_TESTS${NC}"
echo ""

if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "${GREEN}╔═══════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║                                                           ║${NC}"
    echo -e "${GREEN}║   ✓ ВСЕ ТЕСТЫ ПРОЙДЕНЫ УСПЕШНО!                          ║${NC}"
    echo -e "${GREEN}║                                                           ║${NC}"
    echo -e "${GREEN}╚═══════════════════════════════════════════════════════════╝${NC}"
    exit 0
else
    echo -e "${RED}╔═══════════════════════════════════════════════════════════╗${NC}"
    echo -e "${RED}║                                                           ║${NC}"
    echo -e "${RED}║   ✗ НЕКОТОРЫЕ ТЕСТЫ ПРОВАЛЕНЫ                            ║${NC}"
    echo -e "${RED}║                                                           ║${NC}"
    echo -e "${RED}╚═══════════════════════════════════════════════════════════╝${NC}"
    exit 1
fi
