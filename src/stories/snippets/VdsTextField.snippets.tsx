import { Grid } from '@mui/material'
import * as React from 'react'
import { VdsTextField } from '../../vds/VdsTextField/VdsTextField'
import { convert } from '../utils'

//#region standard example
export const standard_example_snippet = convert(`
import React from 'react';
import { VdsTextField } from 'vds-components';

export default () => {

    const [state, setState] = React.useState<{ [P in string]: string | number | null }>({});

    const handleChange = (key: string, value: string | number | null) => { setState({ ...state, [key]: value }); }

    return (
        <VdsTextField
          label='Input text label*'
          value={state.name3}
          error={true}
          errorText='Error message here'
          onChange={(ev) => handleChange('name3', ev.target.value)}
          disabled={true}
          readOnly={true}
        />
    );
}
`);
export const Standard_Example = () => {

  const [state, setState] = React.useState<{ [P in string]: string | number | null }>({});

  const handleChange = (key: string, value: string | number | null) => { setState({ ...state, [key]: value }); }

  return (
    <Grid container spacing={2}>
      <Grid item lg={3}>
        <VdsTextField
          label='Input text label*'
          value={state.name}
          onChange={(ev) => handleChange('name', ev.target.value)}
        />
        <div>
          <h4>Default</h4>
        </div>
      </Grid>
      <Grid item lg={3}>
        <VdsTextField
          label='Input text label*'
          value={state.name1}
          onChange={(ev) => handleChange('name1', ev.target.value)}
          disabled
        />
        <div>
          <h4>Disabled</h4>
        </div>
      </Grid>
      <Grid item lg={3}>
        <VdsTextField
          label='Input text label*'
          value={state.name2}
          onChange={(ev) => handleChange('name2', ev.target.value)}
          readOnly
        />
        <div>
          <h4>ReadOnly</h4>
        </div>
      </Grid>
      <Grid item lg={3}>
        <VdsTextField
          label='Input text label*'
          value={state.name3}
          error={true}
          errorText='Error message here'
          onChange={(ev) => handleChange('name3', ev.target.value)}
        />
        <div>
          <h4>Error</h4>
        </div>
      </Grid>
    </Grid>
  );
}

//#endregion
