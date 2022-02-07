import { Autocomplete, styled, TextField } from '@mui/material';
import * as React from 'react';
import { AiFillMinusCircle } from 'react-icons/ai';

const StyledTextFieldContainer = styled('div')(() => ({
    'display': 'flex',
    'minHeight': '96px',
    'fontFamily': '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen-Sans, Ubuntu, Cantarell, "Helvetica Neue", sans-serif',
    'flexDirection': 'column',
    'input': { padding: '0 !important' }
}));

const StyledInfosContainer = styled('div')({
    'marginBottom': '12px',
    'display': 'flex',
    'flexDirection': 'column'
});

const StyledHelperTextContainer: any = styled('span')(({ disabled }: any) => ({
    'fontSize': "12px",
    'color': disabled ? '#C1C1C4' : "#9DA6AD",
    'lineHeight': "18px",
    'fontFamily': "Roboto",
    'fontWeight': 400,
    'textAlign': "left"
}));

const StyledLabelContainer = styled('span')(({ disabled, readOnly }: any) => ({
    'fontSize': "14px",
    'color': readOnly ? "black" : disabled ? "#9DA6AD" : "#152935",
    'letterSpacing': "0",
    'lineHeight': "18px",
    'fontFamily': "Roboto !important",
    'fontWeight': 500,
    'textAlign': "left",
    'marginBottom': '8px'
}));

const StyledErrorContainer = styled('span')({
    'fontSize': "12px",
    'color': "#D82829",
    'lineHeight': "18px",
    'fontFamily': "Roboto !important",
    'fontWeight': 400,
    display: 'flex',
    alignItems: 'center',
    'textAlign': "left"
});

export const StyledAutocompleteTextField = styled(TextField)(({ disabled, readOnly, error }: any) => ({
    'input': {
        minHeight: '28px',
        'cursor': disabled ? 'not-allowed' : 'text!important',
    },
    '.MuiFilledInput-root': {
        'border': disabled ? '1px solid #C1C1C4' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #C9D9E8',
        'backgroundColor': (disabled || readOnly) ? '#FAFBFD!important' : '#F2F5F8!important',
        paddingTop: '5px!important',
        paddingBottom: '5px!important',
        'font': 'unset',
        'cursor': disabled ? 'not-allowed' : 'text!important',
        borderRadius: 'unset !important'
    },
    '.MuiFilledInput-root:hover': {
        'border': disabled ? '1px solid #0090D1' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #0090D1!important',
        'backgroundColor': (disabled || readOnly) ? '#FAFBFD!important' : '#F2F5F8!important',
    },
    '.MuiFilledInput-root::placeholder': {
        'fontSize': "14px!important",
        'color': (disabled || readOnly) ? "#C1C1C4" : "#9DA6AD",
        'lineHeight': "18px",
        'fontWeight': 400,
        'textAlign': "left"
    },
    '.MuiFilledInput-root::before': {
        'all': 'unset'
    },
    '.MuiFilledInput-root::after': {
        'all': 'unset'
    }
}));

export const VdsAutocomplete = (props: any) => {

    const {
        label,
        errorText,
        error,
        helperText,
        options,
        onChange,
        value,
        disabled,
        noOptionsText,
        getOptionLabel,
        renderTags
    } = props;

    return (
        <StyledTextFieldContainer>
            {(label || helperText) && (
                <StyledInfosContainer>
                    {label && (
                        <StyledLabelContainer>
                            {label}
                        </StyledLabelContainer>
                    )}
                    {helperText && (
                        <StyledHelperTextContainer disabled={disabled}>
                            {helperText}
                        </StyledHelperTextContainer>
                    )}
                </StyledInfosContainer>
            )}
            <Autocomplete
                multiple
                filterSelectedOptions
                options={options}
                getOptionLabel={getOptionLabel}
                value={value}
                onChange={onChange}
                disabled={disabled}
                renderTags={renderTags}
                noOptionsText={noOptionsText}
                ListboxProps={{
                    style: {
                        maxHeight: 224
                    }
                }}
                renderInput={(params) => (
                    <StyledAutocompleteTextField
                        {...params}
                        error={error}
                        variant="filled"
                    />
                )}
            />
            {error && (
                <StyledErrorContainer>
                    <AiFillMinusCircle style={{ fill: '#D82829', fontSize: '13px', padding: '0 5px' }} /> {errorText}
                </StyledErrorContainer>
            )}
        </StyledTextFieldContainer>
    );
}
